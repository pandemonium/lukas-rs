#include "gc.h"

#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

// ===========================================================================
// Garbage collector: generational, conservative mark-sweep, non-moving, backed
// by a slab allocator.
//
// Root finding is conservative for the C call stack and the callee-saved
// registers (spilled with setjmp, then scanned word by word) and precise for
// the globals (runtime builtins + the emitted `gc_user_roots` table). Heap
// tracing is precise. Non-moving, because conservative roots cannot be
// relocated.
//
// Two generations: objects are born young; survivors of a minor collection are
// tenured old. Marmelade values are immutable, so references only run
// young->old -- a minor collection ignores the old generation entirely (no
// write barrier, no remembered set). A major sweeps both.
//
// Allocation is slab-based. Small objects (<= SMALL_MAX bytes, header included)
// are carved from 64 KiB-aligned slabs into fixed-size slots by size class;
// freeing returns a slot to a per-class free-list (no malloc/free per object).
// Larger objects fall back to malloc. The conservative membership test -- "is
// this word the body pointer of a live object?" -- is answered in O(1) and
// maintained *incrementally*: each small object's slot has a bit in its slab's
// allocation bitmap, set in `gc_new` and cleared in the sweep; large objects
// live in a set updated the same way. There is no per-collection rebuild.
// ===========================================================================

// OBJ_TEXT bodies are owned (heap) strings. They have no child Values, so they
// need no tracing -- but they are collectable, unlike borrowed literal strings,
// which live in the program's read-only data and are never GC objects at all.
typedef enum { OBJ_TUPLE, OBJ_CLOSURE, OBJ_TEXT, OBJ_DATA } ObjKind;

// Prepended to every heap object; the Value's `tup`/`clo` points at the body
// just past it, so HEADER/BODY convert between the two.
typedef struct GcHeader {
    struct GcHeader *next; // intrusive list within a generation
    size_t body;           // body size in bytes
    uint8_t mark;
    uint8_t kind; // ObjKind
    uint8_t old;  // 0 = young (nursery), 1 = tenured
} GcHeader;

#define BODY(h) ((void *)((h) + 1))
#define HEADER(p) (((GcHeader *)(p)) - 1)

// ------------------------------------------------------------------ pointer set
// Open-addressing set of pointer-sized keys. 0 = empty, 1 = tombstone (no real
// pointer is either). Used both for slab bases (insert-only) and large-object
// body pointers (insert + remove).
#define PS_TOMB ((uintptr_t)1)
typedef struct {
    uintptr_t *keys;
    size_t cap, count, used;
} PtrSet;

static size_t ps_hash(uintptr_t k, size_t cap) {
    return (size_t)((k >> 4) * 11400714819323198485ull) & (cap - 1);
}

static bool ps_has(PtrSet *s, uintptr_t k) {
    if (!s->keys) return false;
    for (size_t i = ps_hash(k, s->cap); s->keys[i]; i = (i + 1) & (s->cap - 1))
        if (s->keys[i] == k) return true;
    return false;
}

static void ps_put_raw(uintptr_t *keys, size_t cap, uintptr_t k) {
    size_t i = ps_hash(k, cap);
    while (keys[i]) i = (i + 1) & (cap - 1);
    keys[i] = k;
}

static void ps_rehash(PtrSet *s, size_t newcap) {
    uintptr_t *nk = calloc(newcap, sizeof *nk);
    for (size_t i = 0; i < s->cap; i++)
        if (s->keys[i] && s->keys[i] != PS_TOMB) ps_put_raw(nk, newcap, s->keys[i]);
    free(s->keys);
    s->keys = nk;
    s->cap = newcap;
    s->used = s->count;
}

static void ps_insert(PtrSet *s, uintptr_t k) {
    if (!s->keys) {
        s->cap = 1024;
        s->keys = calloc(s->cap, sizeof *s->keys);
    }
    if ((s->used + 1) * 2 > s->cap)
        ps_rehash(s, s->count * 4 > s->cap ? s->cap * 2 : s->cap); // grow, or just drop tombstones
    size_t i = ps_hash(k, s->cap), tomb = (size_t)-1;
    while (s->keys[i]) {
        if (s->keys[i] == k) return;
        if (s->keys[i] == PS_TOMB && tomb == (size_t)-1) tomb = i;
        i = (i + 1) & (s->cap - 1);
    }
    if (tomb != (size_t)-1) {
        s->keys[tomb] = k;
    } else {
        s->keys[i] = k;
        s->used++;
    }
    s->count++;
}

static void ps_remove(PtrSet *s, uintptr_t k) {
    if (!s->keys) return;
    for (size_t i = ps_hash(k, s->cap); s->keys[i]; i = (i + 1) & (s->cap - 1))
        if (s->keys[i] == k) {
            s->keys[i] = PS_TOMB;
            s->count--;
            return;
        }
}

// ------------------------------------------------------------------ slab allocator
#define SLAB_SIZE (64u * 1024)
#define SLAB_MASK (~((uintptr_t)SLAB_SIZE - 1))
#define SMALL_MAX 512               // objects (header+body) up to this are slab-allocated
#define NCLASS (SMALL_MAX / 16 + 1) // size class = round_up(size,16)/16

typedef struct Slab {
    uint32_t slot_size;
    uint32_t slot_count;
    uintptr_t slots;  // first slot address
    uint8_t *bitmap;  // slot_count bits: is this slot allocated?
} Slab;

static void *free_list[NCLASS]; // per-class free slots (intrusive: slot holds next)
static PtrSet slab_set;         // bases of live small slabs (insert-only)
static PtrSet large_set;        // body pointers of live large objects

static Slab *slab_of(uintptr_t slot) { return (Slab *)(slot & SLAB_MASK); }

static void bit_set(uintptr_t slot) {
    Slab *s = slab_of(slot);
    size_t i = (slot - s->slots) / s->slot_size;
    s->bitmap[i >> 3] |= (uint8_t)(1u << (i & 7));
}

static void bit_clear(uintptr_t slot) {
    Slab *s = slab_of(slot);
    size_t i = (slot - s->slots) / s->slot_size;
    s->bitmap[i >> 3] &= (uint8_t) ~(1u << (i & 7));
}

// Allocate a fresh slab for size class `c` and thread its slots onto the free-list.
static void grow_class(size_t c) {
    size_t ss = c * 16;
    Slab *s = aligned_alloc(SLAB_SIZE, SLAB_SIZE);
    uintptr_t base = (uintptr_t)s;
    uintptr_t slots = (base + sizeof(Slab) + 15) & ~(uintptr_t)15;
    s->slot_size = (uint32_t)ss;
    s->slot_count = (uint32_t)((SLAB_SIZE - (slots - base)) / ss);
    s->slots = slots;
    s->bitmap = calloc((s->slot_count + 7) / 8, 1);
    ps_insert(&slab_set, base);
    for (size_t i = 0; i < s->slot_count; i++) {
        void *slot = (void *)(slots + i * ss);
        *(void **)slot = free_list[c];
        free_list[c] = slot;
    }
}

// Conservative membership: is `w` the body pointer of a currently-live object?
// Small objects are validated via their slab's allocation bitmap, large objects
// via the large-object set. O(1), no per-collection scan.
static bool is_object(uintptr_t w) {
    uintptr_t slot = w - sizeof(GcHeader);
    uintptr_t base = slot & SLAB_MASK;
    if (ps_has(&slab_set, base)) {
        Slab *s = (Slab *)base;
        if (slot < s->slots) return false;
        uintptr_t off = slot - s->slots;
        if (off >= (uintptr_t)s->slot_count * s->slot_size) return false;
        if (off % s->slot_size != 0) return false;
        size_t i = off / s->slot_size;
        return (s->bitmap[i >> 3] >> (i & 7)) & 1;
    }
    return ps_has(&large_set, w);
}

// ------------------------------------------------------------------ generations
static GcHeader *gc_young = NULL, *gc_old = NULL;
static size_t gc_young_bytes = 0;      // young allocation since the last minor GC
static size_t gc_old_bytes = 0;        // live bytes tenured in the old generation
static size_t gc_nursery = 16u << 20;  // trigger a minor GC once the nursery fills
static size_t gc_major_at = 8u << 20;  // trigger a major GC once the old gen exceeds this
static bool gc_on = false;
static bool gc_major = false;          // is the in-progress collection a major one?
static bool gc_generational = true;    // MARM_NOGEN=1 forces a full sweep every GC
static bool gc_disabled = false;       // MARM_NOGC=1 never collects (leaks; baseline only)
static void *gc_stack_bottom = NULL;

// Statistics, reported at exit when MARM_GC_STATS is set.
static unsigned long gc_minor_count = 0, gc_major_count = 0;
static unsigned long long gc_total_bytes = 0;
static double gc_time = 0.0;   // seconds spent inside gc_run
static double gc_started = 0.0; // wall clock at gc_init

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

// Mark worklist: explicit, so tracing a deep structure does not recurse (and
// blow) the C stack.
static GcHeader **gc_work = NULL;
static size_t gc_work_len = 0, gc_work_cap = 0;

static void work_push(GcHeader *h) {
    if (gc_work_len == gc_work_cap) {
        gc_work_cap = gc_work_cap ? gc_work_cap * 2 : 256;
        gc_work = realloc(gc_work, gc_work_cap * sizeof *gc_work);
    }
    gc_work[gc_work_len++] = h;
}

static void mark_obj(void *body) {
    GcHeader *h = HEADER(body);
    if (!gc_major && h->old) return; // a minor collection leaves the old gen alone
    if (!h->mark) {
        h->mark = 1;
        work_push(h);
    }
}

static void mark_value(Value v) {
    if (v.tag == TAG_TUPLE) mark_obj(v.tup);
    else if (v.tag == TAG_CLOSURE) mark_obj(v.clo);
    else if (v.tag == TAG_DATA) mark_obj(v.dat);
    // A text is owned (a live OBJ_TEXT body) or borrowed (a literal in read-only
    // data). `is_object` is exactly that distinction -- the &str/String test --
    // so only owned strings are traced; borrowed ones are left alone.
    else if (v.tag == TAG_TEXT && is_object((uintptr_t)v.s)) mark_obj((void *)v.s);
}

// A conservative root candidate: mark it only if it is exactly a live object.
static void mark_candidate(uintptr_t w) {
    if (is_object(w)) mark_obj((void *)w);
}

static void gc_trace(void) {
    while (gc_work_len) {
        GcHeader *h = gc_work[--gc_work_len];
        switch (h->kind) {
        case OBJ_TUPLE: {
            Tuple *t = BODY(h);
            for (size_t i = 0; i < t->len; i++) mark_value(t->elems[i]);
            break;
        }
        case OBJ_CLOSURE: {
            Closure *c = BODY(h);
            for (size_t i = 0; i < c->nfree; i++) mark_value(c->caps[i]);
            break;
        }
        case OBJ_DATA: {
            Data *d = BODY(h);
            size_t len = (h->body - sizeof(Data)) / sizeof(Value);
            for (size_t i = 0; i < len; i++) mark_value(d->fields[i]);
            break;
        }
        case OBJ_TEXT:
            break; // a string body holds no Values -- nothing to trace
        }
    }
}

// The runtime's own global Values -- the curried builtin closures.
static Value *const gc_builtin_roots[] = {
    &builtin_add, &builtin_sub, &builtin_mul, &builtin_div,
    &builtin_mod, &builtin_eq,  &builtin_lt,  &builtin_gt,
    &builtin_le,  &builtin_ge,  &builtin_and, &builtin_or,
    &builtin_xor, &builtin_show, &builtin_print_endline,
    &builtin_text_fold_right,
};

static void scan_words(void *lo, void *hi) {
    uintptr_t *p = (uintptr_t *)((uintptr_t)lo & ~(uintptr_t)(sizeof(void *) - 1));
    for (; p < (uintptr_t *)hi; p++) mark_candidate(*p);
}

// Reclaim a dead object: clear its membership record and recycle its storage.
static void free_object(GcHeader *h) {
    size_t total = sizeof(GcHeader) + h->body;
    if (total <= SMALL_MAX) {
        size_t c = (total + 15) / 16;
        bit_clear((uintptr_t)h);
        *(void **)h = free_list[c]; // back onto the free-list
        free_list[c] = h;
    } else {
        ps_remove(&large_set, (uintptr_t)BODY(h));
        free(h);
    }
}

// One collection. `major` selects a full sweep of both generations; otherwise a
// minor collection sweeps only the nursery, tenuring its survivors.
static void gc_run(bool major) {
    double t0 = now();
    if (major) gc_major_count++;
    else gc_minor_count++;
    gc_major = major;
    jmp_buf regs;
    setjmp(regs); // spill callee-saved registers onto the stack
    void *stack_top = (void *)&regs;

    // Precise roots: runtime builtins and the emitted global table.
    for (size_t i = 0; i < sizeof gc_builtin_roots / sizeof *gc_builtin_roots; i++)
        mark_value(*gc_builtin_roots[i]);
    for (size_t i = 0; i < gc_user_roots_count; i++) mark_value(*gc_user_roots[i]);

    // Conservative roots: the saved registers and the live portion of the stack
    // (which grows down, so `stack_top` is below `gc_stack_bottom`).
    scan_words(&regs, (char *)&regs + sizeof regs);
    scan_words(stack_top, gc_stack_bottom);

    gc_trace();

    if (major) {
        // Survivors keep their generation. Free the unmarked from both lists,
        // unmark and re-thread the survivors, recompute sizes and the threshold.
        size_t young_live = 0, old_live = 0;
        for (GcHeader **link = &gc_young, *h = *link; h; h = *link) {
            if (h->mark) { h->mark = 0; young_live += sizeof(GcHeader) + h->body; link = &h->next; }
            else { *link = h->next; free_object(h); }
        }
        for (GcHeader **link = &gc_old, *h = *link; h; h = *link) {
            if (h->mark) { h->mark = 0; old_live += sizeof(GcHeader) + h->body; link = &h->next; }
            else { *link = h->next; free_object(h); }
        }
        gc_young_bytes = young_live;
        gc_old_bytes = old_live;
        gc_major_at = gc_old_bytes * 2 < (8u << 20) ? (8u << 20) : gc_old_bytes * 2;
    } else {
        // Tenure the survivors: move them from the nursery into the old list.
        GcHeader *h = gc_young;
        gc_young = NULL;
        size_t promoted = 0;
        while (h) {
            GcHeader *next = h->next;
            if (h->mark) {
                h->mark = 0;
                h->old = 1;
                h->next = gc_old;
                gc_old = h;
                promoted += sizeof(GcHeader) + h->body;
            } else {
                free_object(h);
            }
            h = next;
        }
        gc_young_bytes = 0;
        gc_old_bytes += promoted;
    }

    gc_major = false;
    gc_time += now() - t0;
}

// Public entry: force a full collection.
void gc_collect(void) { gc_run(true); }

// Collect if this next allocation would fill the nursery. Called before
// allocating, while the operands are still live on the stack/registers. A minor
// collection that leaves the old generation too large escalates to a major.
static void gc_reserve(size_t need) {
    if (!gc_on || gc_disabled) return;
    if (gc_young_bytes + need > gc_nursery) {
        if (!gc_generational) {
            gc_run(true); // emulate a single-generation collector for comparison
        } else {
            gc_run(false);
            if (gc_old_bytes > gc_major_at) gc_run(true);
        }
    }
}

// Allocate a header + body, born young: a slab slot for small objects, malloc
// for large ones. Records the object in the membership machinery.
static void *gc_new(size_t body, ObjKind kind) {
    size_t total = sizeof(GcHeader) + body;
    GcHeader *h;
    if (total <= SMALL_MAX) {
        size_t c = (total + 15) / 16;
        if (!free_list[c]) grow_class(c);
        void *slot = free_list[c];
        free_list[c] = *(void **)slot;
        bit_set((uintptr_t)slot);
        h = slot;
    } else {
        h = malloc(total);
        ps_insert(&large_set, (uintptr_t)BODY(h));
    }
    h->next = gc_young;
    h->body = body;
    h->mark = 0;
    h->kind = kind;
    h->old = 0;
    gc_young = h;
    gc_young_bytes += total;
    gc_total_bytes += total;
    return BODY(h);
}

static void gc_report(void) {
    double total = now() - gc_started;
    fprintf(stderr,
            "[gc] %lu minor, %lu major; %.1f MB allocated; live old %.1f MB; "
            "nursery %zu KiB\n"
            "[gc] gc %.3fs / total %.3fs -> mutator throughput %.1f%%\n",
            gc_minor_count, gc_major_count, gc_total_bytes / 1048576.0,
            gc_old_bytes / 1048576.0, gc_nursery >> 10, gc_time, total,
            total > 0 ? 100.0 * (total - gc_time) / total : 100.0);
}

void gc_init(void *stack_bottom) {
    gc_started = now();
    gc_stack_bottom = stack_bottom;
    // Generation sizes are tunable (in KiB) for experimentation/benchmarking.
    const char *nursery = getenv("MARM_NURSERY");
    const char *major = getenv("MARM_MAJOR");
    if (nursery) gc_nursery = (size_t)strtoull(nursery, NULL, 10) << 10;
    if (major) gc_major_at = (size_t)strtoull(major, NULL, 10) << 10;
    if (getenv("MARM_NOGEN")) gc_generational = false;
    if (getenv("MARM_NOGC")) gc_disabled = true;
    if (getenv("MARM_GC_STATS")) atexit(gc_report);
    gc_on = true;
}

// Shared builder: allocate a closure with `nfree` inline captures read from the
// (already-started) `va_list`. `gc_reserve` runs before any capture is read, so
// the captures are still live in the caller's argument area (conservatively
// scanned) across the possible collection -- the same discipline as `mk_tuple`.
static Value mk_closure_va(Value (*code)(Value, Value),
                           Value (*worker)(Value, Value *), size_t arity,
                           size_t nfree, va_list ap) {
    size_t body = sizeof(Closure) + nfree * sizeof(Value);
    gc_reserve(sizeof(GcHeader) + body);
    Closure *c = gc_new(body, OBJ_CLOSURE);
    c->code = code;
    c->worker = worker;
    c->arity = arity;
    c->nfree = nfree;
    for (size_t i = 0; i < nfree; i++) {
        c->caps[i] = va_arg(ap, Value);
    }
    Value v;
    v.tag = TAG_CLOSURE;
    v.clo = c;
    return v;
}

Value mk_closure_n(Value (*code)(Value, Value), Value (*worker)(Value, Value *),
                   size_t arity, size_t nfree, ...) {
    va_list ap;
    va_start(ap, nfree);
    Value v = mk_closure_va(code, worker, arity, nfree, ap);
    va_end(ap);
    return v;
}

Value mk_closure(Value (*code)(Value, Value), size_t nfree, ...) {
    va_list ap;
    va_start(ap, nfree);
    Value v = mk_closure_va(code, NULL, 1, nfree, ap);
    va_end(ap);
    return v;
}

// Copy `len` bytes into a fresh, collectable string body (NUL-terminated, so it
// remains a valid C string for `strcmp`/`fputs`). `src` stays live across the
// possible collection in `gc_reserve` because it is on the C stack, which the
// collector scans conservatively.
Value mk_textn(const char *src, size_t len) {
    gc_reserve(sizeof(GcHeader) + len + 1);
    char *body = gc_new(len + 1, OBJ_TEXT);
    memcpy(body, src, len);
    body[len] = '\0';
    Value v;
    v.tag = TAG_TEXT;
    v.s = body;
    return v;
}

// Copy a NUL-terminated C string into a collectable string body.
Value mk_text(const char *src) { return mk_textn(src, strlen(src)); }

Value mk_tuple(size_t len, ...) {
    size_t body = sizeof(Tuple) + len * sizeof(Value);
    gc_reserve(sizeof(GcHeader) + body);
    Tuple *t = gc_new(body, OBJ_TUPLE);
    t->len = len;
    va_list ap;
    va_start(ap, len);
    for (size_t i = 0; i < len; i++) {
        t->elems[i] = va_arg(ap, Value);
    }
    va_end(ap);
    Value v;
    v.tag = TAG_TUPLE;
    v.tup = t;
    return v;
}

Value mk_data(uint64_t tag, size_t nfields, ...) {
    size_t body = sizeof(Data) + nfields * sizeof(Value);
    gc_reserve(sizeof(GcHeader) + body);
    Data *d = gc_new(body, OBJ_DATA);
    d->tag = tag;
    va_list ap;
    va_start(ap, nfields);
    for (size_t i = 0; i < nfields; i++) {
        d->fields[i] = va_arg(ap, Value);
    }
    va_end(ap);
    Value v;
    v.tag = TAG_DATA;
    v.dat = d;
    return v;
}

// Field count of a live constructor value, recovered from its heap header's body
// size (the count is not stored in the object itself).
size_t data_len(Value v) {
    return (HEADER(v.dat)->body - sizeof(Data)) / sizeof(Value);
}
