#include "gc.h"

#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

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
typedef enum {
    OBJ_TUPLE,
    OBJ_CLOSURE,
    OBJ_TEXT,
    OBJ_DATA,
    OBJ_BUFFER, // a stable handle {bytes, len, cap} onto an OBJ_BYTES body
    OBJ_BYTES,  // raw byte body (leaf); a Buffer's bytes, grown by reallocation
    OBJ_MMAP,   // handle to a memory-mapped region (region lives outside the heap)
    OBJ_SLICE,  // immutable view; owner is an OBJ_BYTES body or an OBJ_MMAP handle
} ObjKind;

// Byte-handling bodies (all reached through TAG_OBJECT; GcHeader.kind picks which).
// A Buffer is a STABLE handle onto a separate OBJ_BYTES body: growth reallocates
// the body and updates the handle in place, so the handle's identity never moves
// and a write has nothing to return. A Slice borrows an OBJ_BYTES body or an Mmap
// handle through `owner` (a real GC-body pointer, so the tracer keeps it live)
// plus an offset/length. An Mmap wraps a region that is NOT GC memory.
typedef struct { void *bytes; size_t len; size_t cap; } Buffer;
typedef struct { uint8_t *region; size_t len; bool closed; } Mmap;
typedef struct { void *owner; size_t offset; size_t len; } Slice;

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
static size_t gc_nursery = 256u << 20; // trigger a minor GC once the nursery fills.
// 256 MiB (was 16 MiB): high-churn workloads (e.g. the binary_codec benchmark)
// pay a per-collection fixed cost (a full conservative stack scan) plus
// false-tenuring of transient garbage that is live when a too-frequent minor GC
// fires. A nursery comfortably larger than the working set lets transients die
// young -- measured ~2x total speedup on binary_codec (24s -> 12s), plateauing
// past 256 MiB. NB there is a *valley* around 32-64 MiB (worse than 16) where
// tenuring is pathological, so a moderate bump would regress; jump past it.
// Tunable per run via MARM_NURSERY (KiB).
// A major fires once the old gen exceeds `gc_major_at`, recomputed after each
// major as max(live_old * 2, gc_major_floor). Both are set in gc_init; see the
// note there for why the floor matters.
static size_t gc_major_at = 0;
static size_t gc_major_floor = 0;
// The floor defaults to this many nurseries' worth of bytes.
#define MAJOR_FLOOR_NURSERIES 4
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

// The logical kind of a value, for the runtime's own dispatch. Immediates decode
// from the low bits; a pointer's kind comes from its heap header. Defined here
// (not in runtime.h) because only gc.c sees `GcHeader`/`ObjKind`.
Tag value_tag(Value v) {
    if (v.w & 1) {
        switch (v.w & TAGMASK) {
        case IMM_INT:  return TAG_INT;
        case IMM_BOOL: return TAG_BOOL;
        case IMM_CHAR: return TAG_CHAR;
        default:       return TAG_UNIT; // IMM_UNIT
        }
    }
    switch (HEADER(as_ptr(v))->kind) {
    case OBJ_TEXT:    return TAG_TEXT;
    case OBJ_TUPLE:   return TAG_TUPLE;
    case OBJ_CLOSURE: return TAG_CLOSURE;
    case OBJ_DATA:    return TAG_DATA;
    default:          return TAG_OBJECT; // buffer / bytes / mmap / slice
    }
}

static void mark_value(Value v) {
    // A precise Value: immediates (Int/Bool/Char/Unit) are odd; every even word
    // is a heap body pointer, save 0 (an uninitialised root). No `is_object`
    // membership probe here -- this is the hot trace path, and children of live
    // objects are always valid. (Stage 1b's static-text descriptors will be the
    // one even non-heap case; they get handled when introduced.)
    if (!v.w || (v.w & 1)) return;
    mark_obj(as_ptr(v));
}

// A conservative root candidate: mark it only if it is exactly a live object. An
// odd word can never be a body pointer (bodies are 8-aligned), which also skips
// tagged immediates that happen to sit on the stack -- no false-positive match.
static void mark_candidate(uintptr_t w) {
    if (w & 1) return;
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
        case OBJ_BYTES: // raw bytes, no child Values
        case OBJ_MMAP:  // region pointer + flags, no child Values
            break;
        case OBJ_BUFFER: {
            Buffer *b = BODY(h);
            mark_obj(b->bytes); // handle -> its bytes body
            break;
        }
        case OBJ_SLICE: {
            Slice *s = BODY(h);
            mark_obj(s->owner); // owner is a live OBJ_BYTES body or OBJ_MMAP handle
            break;
        }
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
        size_t twice = gc_old_bytes * 2;
        gc_major_at = twice < gc_major_floor ? gc_major_floor : twice;
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
    // Major-GC trigger: after each major, gc_major_at = max(live_old * 2, floor).
    // The `* 2` (Appel's rule) keeps a major's cost proportional to the live set
    // once it is large; the FLOOR makes major *frequency* track allocation when
    // the live set is small. Without a floor, a flat-memory program that tenures a
    // large transient structure each iteration majors every ~live bytes of
    // tenuring -- often less than one nursery -- reclaiming almost nothing per
    // (live-set-sized) collection (measured: the binary_codec aggressive build did
    // 9-31 near-empty majors and ran 2.7x slower than its leaky self). Flooring at
    // a few nurseries lets that garbage accumulate to a worthwhile slice first.
    // The floor must be computed *after* the nursery is resolved, and it persists
    // across the post-major recompute above (unlike a one-shot gc_major_at seed).
    // MARM_MAJOR (KiB) overrides the floor.
    gc_major_floor = (size_t)MAJOR_FLOOR_NURSERIES * gc_nursery;
    if (major) gc_major_floor = (size_t)strtoull(major, NULL, 10) << 10;
    gc_major_at = gc_major_floor;
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
    return VObject(c);
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
    return VObject(body);
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
    return VObject(t);
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
    return VObject(d);
}

// Field count of a live constructor value, recovered from its heap header's body
// size (the count is not stored in the object itself).
size_t data_len(Value v) {
    return (HEADER(as_ptr(v))->body - sizeof(Data)) / sizeof(Value);
}

// ----------------------------------------------------------------- byte buffers
Value mk_buffer(size_t cap) {
    if (cap == 0) cap = 16;
    gc_reserve(sizeof(GcHeader) + cap);
    void *body = gc_new(cap, OBJ_BYTES); // stays live on the stack across the next reserve
    gc_reserve(sizeof(GcHeader) + sizeof(Buffer));
    Buffer *b = gc_new(sizeof(Buffer), OBJ_BUFFER);
    b->bytes = body;
    b->len = 0;
    b->cap = cap;
    return VObject(b);
}

// A write is a side effect -- nothing to return. The handle never moves: on
// overflow we reallocate the *body* and update the handle in place. `bv` stays
// live on the stack across the collection `gc_new` may trigger, and the handle
// keeps the old body live through its trace, so the memcpy source survives.
void buffer_put_u8(Value bv, uint8_t byte) {
    Buffer *b = as_ptr(bv);
    if (b->len == b->cap) {
        size_t ncap = b->cap * 2;
        gc_reserve(sizeof(GcHeader) + ncap);
        void *nbody = gc_new(ncap, OBJ_BYTES);
        b = as_ptr(bv);
        memcpy(nbody, b->bytes, b->len);
        b->bytes = nbody;
        b->cap = ncap;
    }
    ((uint8_t *)b->bytes)[b->len++] = byte;
}

void buffer_put_bytes(Value bv, const uint8_t *src, size_t n) {
    for (size_t i = 0; i < n; i++) buffer_put_u8(bv, src[i]);
}

size_t buffer_len(Value bv) { return ((Buffer *)as_ptr(bv))->len; }

// Typed writes: append a width's worth of bytes in the given order. Signed and
// unsigned share the same bytes, so one entry per (width, endianness).
#define BUFFER_PUT_LE(NAME, N)                                                          \
    void NAME(Value bv, int64_t v) {                                                    \
        uint64_t u = (uint64_t)v;                                                       \
        for (size_t k = 0; k < (N); k++) buffer_put_u8(bv, (uint8_t)(u >> (8 * k)));    \
    }
#define BUFFER_PUT_BE(NAME, N)                                                          \
    void NAME(Value bv, int64_t v) {                                                    \
        uint64_t u = (uint64_t)v;                                                       \
        for (size_t k = 0; k < (N); k++)                                                \
            buffer_put_u8(bv, (uint8_t)(u >> (8 * ((N) - 1 - k))));                     \
    }
BUFFER_PUT_LE(buffer_put_16_le, 2)
BUFFER_PUT_LE(buffer_put_32_le, 4)
BUFFER_PUT_LE(buffer_put_64_le, 8)
BUFFER_PUT_BE(buffer_put_16_be, 2)
BUFFER_PUT_BE(buffer_put_32_be, 4)
BUFFER_PUT_BE(buffer_put_64_be, 8)

// Append a slice's bytes (slice_len/slice_get_u8 are declared in gc.h, defined below).
void buffer_put_slice(Value bv, Value sv) {
    size_t n = slice_len(sv);
    for (size_t i = 0; i < n; i++) buffer_put_u8(bv, slice_get_u8(sv, i));
}

Value mk_slice(void *owner, size_t offset, size_t len) {
    // `owner` is a body pointer; it sits on the stack (conservatively scanned), so
    // it survives the collection `gc_reserve` may trigger.
    gc_reserve(sizeof(GcHeader) + sizeof(Slice));
    Slice *s = gc_new(sizeof(Slice), OBJ_SLICE);
    s->owner = owner;
    s->offset = offset;
    s->len = len;
    return VObject(s);
}

// Hand the buffer's body to a Slice, then reseed the handle with a fresh empty
// body so it no longer aliases the bytes it gave away.
Value buffer_move(Value bv) {
    Buffer *b = as_ptr(bv);
    size_t len = b->len;
    void *body = b->bytes; // handed off below; stays live on the stack meanwhile
    gc_reserve(sizeof(GcHeader) + 16);
    void *fresh = gc_new(16, OBJ_BYTES);
    b = as_ptr(bv);
    b->bytes = fresh;
    b->len = 0;
    b->cap = 16;
    return mk_slice(body, 0, len);
}

Value buffer_copy(Value bv) {
    size_t n = ((Buffer *)as_ptr(bv))->len;
    gc_reserve(sizeof(GcHeader) + (n ? n : 1));
    void *body = gc_new(n ? n : 1, OBJ_BYTES);
    Buffer *b = as_ptr(bv); // re-fetch after the possible collection
    memcpy(body, b->bytes, n);
    return mk_slice(body, 0, n);
}

static const uint8_t *slice_base(Slice *s) {
    GcHeader *h = HEADER(s->owner);
    if (h->kind == OBJ_BYTES) return (const uint8_t *)s->owner + s->offset;
    return ((Mmap *)s->owner)->region + s->offset; // OBJ_MMAP
}

size_t slice_len(Value sv) { return ((Slice *)as_ptr(sv))->len; }

uint8_t slice_get_u8(Value sv, size_t i) { return slice_base(as_ptr(sv))[i]; }

Value slice_sub(Value sv, size_t off, size_t len) {
    Slice *s = as_ptr(sv);
    return mk_slice(s->owner, s->offset + off, len); // shares the owner
}

#define SLICE_GET_LE(NAME, TYPE, N)                                                    \
    TYPE NAME(Value sv, size_t off) {                                                  \
        const uint8_t *p = slice_base(as_ptr(sv)) + off;                                    \
        uint64_t v = 0;                                                                \
        for (size_t k = 0; k < (N); k++) v |= (uint64_t)p[k] << (8 * k);               \
        return (TYPE)v;                                                                \
    }
#define SLICE_GET_BE(NAME, TYPE, N)                                                    \
    TYPE NAME(Value sv, size_t off) {                                                  \
        const uint8_t *p = slice_base(as_ptr(sv)) + off;                                    \
        uint64_t v = 0;                                                                \
        for (size_t k = 0; k < (N); k++) v = (v << 8) | p[k];                          \
        return (TYPE)v;                                                                \
    }
SLICE_GET_LE(slice_get_u16_le, uint16_t, 2)
SLICE_GET_LE(slice_get_u32_le, uint32_t, 4)
SLICE_GET_LE(slice_get_u64_le, uint64_t, 8)
SLICE_GET_LE(slice_get_i16_le, int16_t, 2)
SLICE_GET_LE(slice_get_i32_le, int32_t, 4)
SLICE_GET_LE(slice_get_i64_le, int64_t, 8)
SLICE_GET_BE(slice_get_u16_be, uint16_t, 2)
SLICE_GET_BE(slice_get_u32_be, uint32_t, 4)
SLICE_GET_BE(slice_get_u64_be, uint64_t, 8)
SLICE_GET_BE(slice_get_i16_be, int16_t, 2)
SLICE_GET_BE(slice_get_i32_be, int32_t, 4)
SLICE_GET_BE(slice_get_i64_be, int64_t, 8)

// ----------------------------------------------------------------- memory maps
// Result ordinals follow `Result ::= Fault e | Return a` -> Fault = 0, Return = 1.
// (Verify against codegen's constructor numbering before wiring the stdlib.)
static Value result_return(Value x) { return mk_data(1, 1, x); }
static Value result_fault(Value e) { return mk_data(0, 1, e); }

// Ranged Buffer -> Bytes producers. Like buffer_move/buffer_copy but for a
// sub-range [off, off+n); Fault(-1) if that range runs past the buffer's length.
Value buffer_move_range(Value bv, size_t off, size_t n) {
    Buffer *b = as_ptr(bv);
    if (off + n > b->len) return result_fault(VInt(-1));
    void *body = b->bytes; // handed off below; stays live on the stack meanwhile
    gc_reserve(sizeof(GcHeader) + 16);
    void *fresh = gc_new(16, OBJ_BYTES);
    b = as_ptr(bv);
    b->bytes = fresh;
    b->len = 0;
    b->cap = 16;
    return result_return(mk_slice(body, off, n));
}

Value buffer_copy_range(Value bv, size_t off, size_t n) {
    Buffer *b = as_ptr(bv);
    if (off + n > b->len) return result_fault(VInt(-1));
    gc_reserve(sizeof(GcHeader) + (n ? n : 1));
    void *body = gc_new(n ? n : 1, OBJ_BYTES);
    b = as_ptr(bv); // re-fetch after the possible collection
    memcpy(body, (const uint8_t *)b->bytes + off, n);
    return result_return(mk_slice(body, 0, n));
}

static Value mk_mmap(uint8_t *region, size_t len) {
    gc_reserve(sizeof(GcHeader) + sizeof(Mmap));
    Mmap *m = gc_new(sizeof(Mmap), OBJ_MMAP);
    m->region = region;
    m->len = len;
    m->closed = false;
    return VObject(m);
}

Value mmap_open(const char *path) {
    int fd = open(path, O_RDONLY);
    if (fd < 0) return result_fault(VInt(errno));
    struct stat st;
    if (fstat(fd, &st) < 0) {
        int e = errno;
        close(fd);
        return result_fault(VInt(e));
    }
    size_t len = (size_t)st.st_size;
    void *region = mmap(NULL, len, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd); // the mapping outlives the fd
    if (region == MAP_FAILED) return result_fault(VInt(errno));
    return result_return(mk_mmap(region, len));
}

void mmap_close(Value mv) {
    Mmap *m = as_ptr(mv);
    if (!m->closed) {
        munmap(m->region, m->len);
        m->closed = true;
    }
}

Value mmap_read(Value mv, size_t off, size_t n) {
    Mmap *m = as_ptr(mv);
    if (m->closed || off + n > m->len) return result_fault(VInt(-1));
    Value bufv = mk_buffer(n);
    Buffer *b = as_ptr(bufv);
    m = as_ptr(mv); // re-fetch after the possible collection in mk_buffer
    memcpy(b->bytes, m->region + off, n);
    b->len = n;
    return result_return(buffer_move(bufv));
}

// Zero-copy view into a mapped region: a Slice whose owner is the Mmap handle
// itself (no copy -- `slice_base` reads straight from `region`). Valid only
// while the mapping is open; reading it after mmap_close faults on the unmapped
// pages. Returns Result (Fault errno | Return Slice).
Value mmap_slice(Value mv, size_t off, size_t n) {
    Mmap *m = as_ptr(mv);
    if (m->closed || off + n > m->len) return result_fault(VInt(-1));
    return result_return(mk_slice(m, off, n)); // owner = the OBJ_MMAP handle
}

// Direct reads on a mapped region (for Byte_Source Mmap -- zero-copy, no Slice).
int64_t mmap_len(Value mv) { return (int64_t)((Mmap *)as_ptr(mv))->len; }
int64_t mmap_get_u8(Value mv, int64_t i) { return (int64_t)((Mmap *)as_ptr(mv))->region[i]; }
bool    mmap_is_closed(Value mv) { return ((Mmap *)as_ptr(mv))->closed; }

// Write a slice's bytes to `path` (truncating). Returns 0 on success, else errno.
int64_t slice_write_file(Value sv, const char *path) {
    Slice *s = as_ptr(sv);
    FILE *f = fopen(path, "wb");
    if (!f) return errno;
    size_t w = fwrite(slice_base(s), 1, s->len, f);
    int err = (w == s->len) ? 0 : -1;
    fclose(f);
    return err;
}
