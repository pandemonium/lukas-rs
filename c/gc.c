#include "gc.h"

#include <assert.h>
#include <setjmp.h>
#include <stddef.h>
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
// tenured old. Most Marmelade values are immutable. Mutable buffers and flat
// arrays use a write barrier and remembered set for old->young references, so a
// minor collection scans those containers while otherwise ignoring the old
// generation. A major sweeps both.
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

// `ObjKind`, `GcHeader`, and the `HEADER`/`BODY` macros now live in gc.h (shared
// with the emitted code, which needs them to build static text descriptors for
// borrowed string literals -- see notes/tagged-value.md Stage 1b). OBJ_TEXT
// bodies are owned (heap) strings with no child Values (no tracing); borrowed
// literals live in .rodata behind a MARM_ETERNAL descriptor and are never GC
// objects at all.

// Byte-handling bodies (all reached through TAG_OBJECT; GcHeader.kind picks which).
// A Buffer is a STABLE handle onto a separate OBJ_BYTES body: growth reallocates
// the body and updates the handle in place, so the handle's identity never moves
// and a write has nothing to return. A Slice borrows an OBJ_BYTES body or an Mmap
// handle through `owner` (a real GC-body pointer, so the tracer keeps it live)
// plus an offset/length. An Mmap wraps a region that is NOT GC memory.
typedef struct { void *bytes; size_t len; size_t cap; } Buffer;
typedef struct { uint8_t *region; size_t len; bool closed; } Mmap;
// `Slice` moved to gc.h so emitted code can build a static .rodata Text (a Slice over a
// static OBJ_BYTES body) the same way it builds other immortal descriptors.

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

// Immix mark-region heap (the default; opt back to the slab collector with
// MARM_GC=slab): a bump-allocated, non-moving, block/line collector that reclaims
// by whole free lines/blocks -- never touching a dead object. Selected at startup.
// Defined further down (needs the generation globals); forward-declared here for
// the dispatch in `is_object` / `gc_new`.
static bool gc_immix = true;
static void *gc_alloc_slow(size_t total, ObjKind kind);
static bool is_object_immix(uintptr_t w);
static void ix_mark_lines(void *body); // mark the lines a live object spans
static void ix_reset_lines(void);      // clear data-line marks before a collection
static void ix_reclaim(void);          // free empty lines, keep occupied ones
static size_t ix_bytes;                // bytes allocated since the last immix collection
static size_t ix_threshold;            // collect once ix_bytes crosses this (Appel: 2x live)

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
// `cold`/`noinline`: this fires only when a size class runs dry (once per thousands
// of allocations), so keeping it out of line shrinks `gc_new`'s hot-path frame --
// which in turn lets `gc_new` itself inline into the fixed-arity constructors below.
static __attribute__((noinline, cold)) void grow_class(size_t c) {
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
    if (gc_immix) return is_object_immix(w);
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
// Small (slab-allocated) objects carry NO generation-list link: the sweep
// enumerates them by walking each slab's allocation bitmap in address order --
// sequential and cache-friendly, versus chasing a per-object list scattered across
// the whole nursery (a cache miss per object, the dominant minor-GC cost). The
// `old` header flag distinguishes young from tenured in place. Only large objects
// (not slab-backed, and rare) keep an explicit list.
// Large (malloc'd) objects, both generations. A side array rather than an intrusive
// header link, so the common small object no longer pays for a `next` field. Large
// objects are rare, so a growable array (compacted at each sweep) is ample.
static GcHeader **gc_large = NULL;
static size_t gc_large_len = 0, gc_large_cap = 0;
static void large_push(GcHeader *h) {
    if (gc_large_len == gc_large_cap) {
        gc_large_cap = gc_large_cap ? gc_large_cap * 2 : 16;
        gc_large = realloc(gc_large, gc_large_cap * sizeof *gc_large);
    }
    gc_large[gc_large_len++] = h;
}
static size_t gc_young_bytes = 0;      // young allocation since the last minor GC
static size_t gc_old_bytes = 0;        // live bytes tenured in the old generation

// Generational write barrier for mutable heap objects. Buffers mutate their raw
// `bytes` child and flat arrays mutate Value leaves. Once such a container has
// tenured, a store may create an old->young edge which a minor collection would
// otherwise miss. Remember the old container and trace its children explicitly
// on each minor; dead entries are pruned by the next major collection.
static uintptr_t *gc_rem = NULL; // body pointers of old mutated containers
static size_t gc_rem_len = 0, gc_rem_cap = 0;

static void gc_remember_object(void *body) {
    if (!HEADER(body)->old) return; // young container: a minor traces it anyway
    for (size_t i = 0; i < gc_rem_len; i++)
        if (gc_rem[i] == (uintptr_t)body) return; // already remembered
    if (gc_rem_len == gc_rem_cap) {
        gc_rem_cap = gc_rem_cap ? gc_rem_cap * 2 : 16;
        gc_rem = realloc(gc_rem, gc_rem_cap * sizeof *gc_rem);
    }
    gc_rem[gc_rem_len++] = (uintptr_t)body;
}

static void gc_prune_remembered(void) {
    size_t kept = 0;
    for (size_t i = 0; i < gc_rem_len; i++)
        if (is_object(gc_rem[i])) gc_rem[kept++] = gc_rem[i];
    gc_rem_len = kept;
}
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
static double gc_time = 0.0;   // seconds spent inside gc_run (collection)
static double alloc_time = 0.0; // seconds in the allocation slow path, EXCLUDING any
                                // collection it triggered (run/block refill overhead);
                                // the fast bump in gc_new is folded into mutator time
static double gc_started = 0.0; // wall clock at gc_init

// Allocation histogram (MARM_ALLOC_STATS): count + bytes by kind and arity. This is
// the B5 opportunity measurement -- how much allocation is 2-tuples (State pairs),
// closures (bind continuations), and small data (Results), i.e. what struct-return
// State + stack closures would remove. Gated: a single predictable branch off the hot
// path, no effect unless MARM_ALLOC_STATS is set.
static bool gc_alloc_stats = false;
#define ALLOC_MAX_ARITY 16
static unsigned long long alloc_hist_n[OBJ_KIND_COUNT][ALLOC_MAX_ARITY + 1];
static unsigned long long alloc_hist_b[OBJ_KIND_COUNT][ALLOC_MAX_ARITY + 1];
static void alloc_record(ObjKind kind, size_t total) {
    size_t body = total - sizeof(GcHeader), arity = 0;
    switch (kind) {
    case OBJ_TUPLE:   arity = body / sizeof(Value); break;
    case OBJ_DATA:    arity = (body - sizeof(Data)) / sizeof(Value); break;    // fields (no tag)
    case OBJ_CLOSURE: arity = (body - sizeof(Closure)) / sizeof(Value); break; // captures
    default: break;
    }
    if (arity > ALLOC_MAX_ARITY) arity = ALLOC_MAX_ARITY;
    alloc_hist_n[kind][arity]++;
    alloc_hist_b[kind][arity] += total;
}

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
    // A static text descriptor (borrowed literal, Stage 1b): it lives `const` in
    // .rodata, so it must never be marked (the write would fault) or freed. It can
    // only be reached here, as a child Value of a heap object; the conservative
    // scan and sweep never see it (`is_object` is false, it's on no gen list).
    if (h->old == MARM_ETERNAL) return;
    if (!gc_major && h->old) return; // a minor collection leaves the old gen alone
    if (!h->mark) {
        h->mark = 1;
        work_push(h);
        if (gc_immix) ix_mark_lines(body); // keep the lines this object spans
    }
}

// `value_tag` is gone: the word no longer tags *which* immediate a value is, and the
// runtime's two former consumers are now representation-driven instead -- `val_eq`
// compares immediates by word identity and pointers by `GcHeader.kind`, and `prim_show`
// is monomorphised per-type at codegen. `GcHeader.kind` (the OBJ_* kinds) is untouched;
// the GC still dispatches its field tracing on it.

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
            size_t len = h->body / sizeof(Value); // count recovered from body size
            for (size_t i = 0; i < len; i++) mark_value(t->elems[i]);
            break;
        }
        case OBJ_CLOSURE: {
            Closure *c = BODY(h);
            size_t nfree = (h->body - sizeof(Closure)) / sizeof(Value); // count from body
            for (size_t i = 0; i < nfree; i++) mark_value(c->caps[i]); // desc is static, not traced
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
        case OBJ_FLOAT: // a boxed double, no child Values
            break;
        case OBJ_BUFFER: {
            Buffer *b = BODY(h);
            mark_obj(b->bytes); // handle -> its bytes body
            break;
        }
        case OBJ_SLICE: {
            Slice *s = BODY(h);
            // owner is a live OBJ_BYTES body / OBJ_MMAP handle / another OBJ_SLICE, or
            // NULL for an inline-owned slice (its bytes live in this object -- no child).
            if (s->owner) mark_obj(s->owner);
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
    &builtin_xor, &builtin_print_endline,
    &builtin_text_fold_right,
};

// Conservatively scan a word range for roots. This deliberately reads EVERY word in
// [lo, hi) -- for a stack scan that includes the compiler's inter-variable padding and,
// under AddressSanitizer, its poisoned stack redzones. Reading those is intentional and
// safe (they are real, mapped stack memory), so this function is exempted from ASan's
// checks; the heap accesses it drives (via `mark_candidate` -> `is_object`) stay checked.
__attribute__((no_sanitize("address")))
static void scan_words(void *lo, void *hi) {
    uintptr_t *p = (uintptr_t *)((uintptr_t)lo & ~(uintptr_t)(sizeof(void *) - 1));
    for (; p < (uintptr_t *)hi; p++) mark_candidate(*p);
}

// Reclaim a dead object: clear its membership record and recycle its storage.
static void free_object(GcHeader *h) {
    // An OBJ_MMAP handle owns an OS mapping. Reclaim it here, when the collector
    // frees the (now unreachable) handle -- a borrowed Bytes/Text view keeps the
    // handle alive through its traced `owner`, so the mapping stays valid exactly
    // as long as something references it, and is unmapped once nothing does. This
    // is the mapping's destructor, not a general finalizer: no user code, no
    // resurrection, just the `munmap` that pairs with the handle's `free` (the
    // same shape as the `free()` a large object gets below). `mmap_close` is the
    // rare explicit opt-in that unmaps eagerly; its `closed` flag guards a double
    // unmap here.
    if (h->kind == OBJ_MMAP) {
        Mmap *m = BODY(h);
        if (!m->closed) munmap(m->region, m->len);
    }
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

// Sweep the slab-allocated (small) objects by walking every slab's allocation
// bitmap in address order. Live young objects tenure in place (set `old`); dead
// ones are freed; a minor skips the old gen. Sequential over dense bitmaps and
// contiguous slots -- so an object is already in cache for both its mark read and
// its free-list write, which is the whole point versus the scattered list walk.
// Adds surviving bytes to `*young_live` / `*old_live` by generation.
static void sweep_small(bool major, size_t *young_live, size_t *old_live) {
    for (size_t si = 0; si < slab_set.cap; si++) {
        uintptr_t base = slab_set.keys ? slab_set.keys[si] : 0;
        if (!base || base == PS_TOMB) continue;
        Slab *s = (Slab *)base;
        // Walk the bitmap a byte (8 slots) at a time: one load per 8 slots, and a
        // whole empty byte skips 8 free slots with a single branch -- most of the
        // per-slot overhead the scattered list walk did not have. `bits` is a copy,
        // so `free_object` clearing the live bitmap underneath does not disturb it.
        uint32_t nbytes = (s->slot_count + 7) / 8;
        for (uint32_t byte = 0; byte < nbytes; byte++) {
            uint8_t bits = s->bitmap[byte];
            if (!bits) continue; // 8 free slots
            for (uint32_t k = 0; k < 8; k++) {
                if (!((bits >> k) & 1)) continue;
                uint32_t i = byte * 8 + k;
                if (i >= s->slot_count) break;
                GcHeader *h = (GcHeader *)(s->slots + (uintptr_t)i * s->slot_size);
                if (!major && h->old) continue; // minor: leave the old gen alone
                size_t sz = sizeof(GcHeader) + h->body;
                if (h->mark) {
                    h->mark = 0;
                    if (!major) { h->old = 1; *old_live += sz; } // tenure young survivors
                    else if (h->old) *old_live += sz;
                    else *young_live += sz;
                } else {
                    free_object(h); // clears this slot's bitmap bit + recycles it
                }
            }
        }
    }
}

// The large-object companion to sweep_small: a short intrusive list (large objects
// are rare, so a list is fine and there is no slab to bitmap-scan).
static void sweep_large(bool major, size_t *young_live, size_t *old_live) {
    size_t w = 0; // compact survivors to the front of the array in place
    for (size_t i = 0; i < gc_large_len; i++) {
        GcHeader *h = gc_large[i];
        if (!major && h->old) { gc_large[w++] = h; continue; }
        size_t sz = sizeof(GcHeader) + h->body;
        if (h->mark) {
            h->mark = 0;
            if (!major) { h->old = 1; *old_live += sz; }
            else if (h->old) *old_live += sz;
            else *young_live += sz;
            gc_large[w++] = h;
        } else {
            free_object(h);
        }
    }
    gc_large_len = w;
}

// One collection. `major` selects a full sweep of both generations; otherwise a
// minor collection sweeps only the nursery, tenuring its survivors.
static void gc_run(bool major) {
    double t0 = now();
    if (major) gc_major_count++;
    else gc_minor_count++;
    gc_major = major;
    if (gc_immix) ix_reset_lines(); // clear line marks so the trace rebuilds liveness
    jmp_buf regs;
    // `setjmp` is used ONLY for its side effect: it spills the callee-saved registers
    // into `regs`, which we then scan conservatively (a live pointer may sit only in a
    // register). There is no matching `longjmp`, so the return value is intentionally
    // discarded -- the `(void)` cast documents that and quiets unused-return linters.
    (void)setjmp(regs); // NOLINT(bugprone-unused-return-value): spill-only, no longjmp
    void *stack_top = (void *)&regs;

    // Precise roots: runtime builtins and the emitted global table.
    for (size_t i = 0; i < sizeof gc_builtin_roots / sizeof *gc_builtin_roots; i++)
        mark_value(*gc_builtin_roots[i]);
    for (size_t i = 0; i < gc_user_roots_count; i++) mark_value(*gc_user_roots[i]);

    // Conservative roots: the saved registers and the live portion of the stack
    // (which grows down, so `stack_top` is below `gc_stack_bottom`).
    scan_words(&regs, (char *)&regs + sizeof regs);
    scan_words(stack_top, gc_stack_bottom);

    // Write-barrier roots. A minor skips each old container itself, so trace its
    // mutable children directly and enqueue any young objects they reference.
    if (!major) {
        for (size_t i = 0; i < gc_rem_len; i++) {
            void *body = (void *)gc_rem[i];
            GcHeader *h = HEADER(body);
            if (h->kind == OBJ_BUFFER) {
                mark_obj(((Buffer *)body)->bytes);
            } else if (h->kind == OBJ_TUPLE) {
                Tuple *t = body;
                size_t len = h->body / sizeof(Value);
                for (size_t j = 0; j < len; j++) mark_value(t->elems[j]);
            }
        }
    }

    gc_trace();

    if (gc_immix) {
        ix_reclaim(); // mark-region: free empty lines/keep occupied ones, no per-object free
        // Reclaim clears dead object-start bits. Drop their remembered entries
        // before the next collection tries to inspect the container kind.
        gc_prune_remembered();
    } else if (major) {
        // Full sweep of both generations. Survivors keep their generation; the dead
        // are freed. Bitmap-walk the small objects, list-walk the large ones.
        size_t young_live = 0, old_live = 0;
        sweep_small(true, &young_live, &old_live);
        sweep_large(true, &young_live, &old_live);
        // Prune containers this major freed from the remembered set: their
        // old->young edge is gone. `is_object` is false once free_object cleared
        // the slot's bit.
        gc_prune_remembered();
        gc_young_bytes = young_live;
        gc_old_bytes = old_live;
        size_t twice = gc_old_bytes * 2;
        gc_major_at = twice < gc_major_floor ? gc_major_floor : twice;
    } else {
        // Minor: young survivors tenure in place (the sweep sets `old`); the dead
        // are freed. `promoted` is the tenured bytes; nothing stays young.
        size_t young_live = 0, promoted = 0;
        sweep_small(false, &young_live, &promoted);
        sweep_large(false, &young_live, &promoted);
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
    if (gc_immix) {
        // Collect once allocation since the last collection crosses the adaptive
        // threshold (Appel: ~2x the live set, floored at one nursery). This keeps a
        // whole-heap trace cheap-per-garbage on a large stable live set (the codec)
        // while staying frequent when little survives (utf8_get).
        if (ix_bytes + need > ix_threshold) gc_run(false);
        return;
    }
    if (gc_young_bytes + need > gc_nursery) {
        if (!gc_generational) {
            gc_run(true); // emulate a single-generation collector for comparison
        } else {
            gc_run(false);
            if (gc_old_bytes > gc_major_at) gc_run(true);
        }
    }
}

// ============================ Immix mark-region heap ========================
// 32 KiB blocks divided into 128 B lines. Small/medium objects bump-allocate
// through a block's free lines; larger objects share the malloc'd large-object
// path. Non-moving, so conservative roots just work (an ambiguous pointer keeps
// its object's line live -- nothing to rewrite). See notes/gc-design.md Option 1.
#define IX_BLOCK (32u * 1024)
#define IX_LINE  128u
#define IX_LINES (IX_BLOCK / IX_LINE)      // 256 lines / block
#define IX_MASK  (~((uintptr_t)IX_BLOCK - 1))
#define IX_MAX_ALLOC (IX_LINE * 4u)        // bigger than this -> large-object space

typedef struct IxBlock {
    struct IxBlock *next;            // link over every block, for reclaim iteration
    struct IxBlock *rnext;           // recyclable list: blocks with free lines to bump into
    uint8_t line[IX_LINES];          // per line: occupied? (rebuilt each collection)
    uint8_t start[IX_BLOCK / 8 / 8]; // object-start bitmap, 1 bit per 8 B (conservative)
    uint32_t data_line;              // first data line (past this header)
} IxBlock;

#define IX_GBYTES (IX_LINE / 8u / 8u)      // object-start bytes per line (16 granules = 2)

static IxBlock *ix_blocks = NULL, *ix_tail = NULL; // all blocks, in allocation order
static IxBlock *ix_recycle = NULL;         // blocks with free lines (rebuilt each collection)
static PtrSet ix_set;                      // block bases, O(1) conservative membership
static IxBlock *ix_cur = NULL;             // block currently being bump-filled
static uintptr_t ix_ptr = 0, ix_limit = 0; // bump cursor + end of the current free run
static uintptr_t ix_run = 0;               // start of the current run (for bulk line marking)
static size_t ix_bytes = 0;                // bytes allocated since the last collection

static inline void ix_set_start(IxBlock *b, uintptr_t body) {
    size_t g = (body - (uintptr_t)b) / 8;
    b->start[g >> 3] |= (uint8_t)(1u << (g & 7));
}
static inline bool ix_is_start(IxBlock *b, uintptr_t body) {
    size_t g = (body - (uintptr_t)b) / 8;
    return (b->start[g >> 3] >> (g & 7)) & 1;
}

static IxBlock *ix_new_block(void) {
    IxBlock *b = aligned_alloc(IX_BLOCK, IX_BLOCK);
    memset(b->line, 0, sizeof b->line);
    memset(b->start, 0, sizeof b->start);
    b->data_line = (uint32_t)((sizeof(IxBlock) + IX_LINE - 1) / IX_LINE);
    for (uint32_t i = 0; i < b->data_line; i++) b->line[i] = 1; // header lines: always occupied
    b->next = NULL;
    if (ix_tail) ix_tail->next = b; else ix_blocks = b; // append, so the alloc walk is linear
    ix_tail = b;
    ps_insert(&ix_set, (uintptr_t)b);
    return b;
}

// Find the first run of free lines in `b` at/after line `from`; return its byte
// range via out-params. Pure (no globals), so the allocator can probe blocks.
static bool ix_find_run(IxBlock *b, uint32_t from, uintptr_t *s, uintptr_t *e) {
    uint32_t i = from;
    while (i < IX_LINES && b->line[i]) i++;         // skip occupied lines
    if (i >= IX_LINES) return false;
    uint32_t j = i;
    while (j < IX_LINES && !b->line[j]) j++;         // extent of the free run
    *s = (uintptr_t)b + (uintptr_t)i * IX_LINE;
    *e = (uintptr_t)b + (uintptr_t)j * IX_LINE;
    return true;
}

// Cold allocation path: the fast bump in `gc_new` fell through because the current
// run is exhausted, the object is large, or the slab collector is selected. Do the
// collection trigger (`gc_reserve`), then allocate + initialise the header. Kept out
// of line (and never inlined) so `gc_new`'s fast path folds into the fixed-arity
// constructors as a tight bump with no call. `total` arrives already 8-rounded.
static __attribute__((noinline)) void *gc_alloc_slow(size_t total, ObjKind kind) {
    double slow_t0 = now();
    double gc_before = gc_time; // subtract any collection triggered below
    gc_reserve(total); // Appel (immix) / nursery (slab) threshold: collect if due
    GcHeader *h;
    if (gc_immix) {
        if (total > IX_MAX_ALLOC) {                 // large: malloc, shared large path
            assert(total - sizeof(GcHeader) <= UINT32_MAX); // body is uint32 (see GcHeader)
            h = malloc(total);
            ps_insert(&large_set, (uintptr_t)BODY(h));
            large_push(h);
        } else {
            while (ix_ptr + total > ix_limit) {
                // Leaving the current run: bulk-mark the lines we filled as occupied, in
                // one memset, so `ix_find_run` never re-fills them. Doing this per run
                // (not per object) is the Phase-3 win.
                if (ix_cur && ix_ptr > ix_run) {
                    uint32_t a = (uint32_t)((ix_run - (uintptr_t)ix_cur) / IX_LINE);
                    uint32_t z = (uint32_t)((ix_ptr - 1 - (uintptr_t)ix_cur) / IX_LINE);
                    memset(ix_cur->line + a, 1, z - a + 1);
                }
                uintptr_t s, e;
                if (ix_cur) {                        // more free lines forward in this block?
                    uint32_t from = (uint32_t)((ix_limit - (uintptr_t)ix_cur) / IX_LINE);
                    if (from < IX_LINES && ix_find_run(ix_cur, from, &s, &e)) {
                        ix_ptr = s; ix_limit = e; ix_run = s; continue;
                    }
                }
                // Next block with free lines: pop the recyclable list (never walks full
                // blocks -- that was O(blocks) per fill), else grow a fresh block.
                if (ix_recycle) { ix_cur = ix_recycle; ix_recycle = ix_recycle->rnext; }
                else ix_cur = ix_new_block();
                (void)ix_find_run(ix_cur, ix_cur->data_line, &s, &e); // recyclable/fresh => a run
                ix_ptr = s; ix_limit = e; ix_run = s;
            }
            h = (GcHeader *)ix_ptr;
            ix_ptr += total;
            ix_set_start(ix_cur, (uintptr_t)BODY(h));
        }
        ix_bytes += total; // accumulated into gc_total_bytes at each reclaim (stats)
    } else {
        // Slab collector (non-default): every allocation lands here.
        if (total <= SMALL_MAX) {
            size_t c = (total + 15) / 16;
            if (!free_list[c]) grow_class(c);
            void *slot = free_list[c];
            free_list[c] = *(void **)slot;
            bit_set((uintptr_t)slot);
            h = slot;
        } else {
            assert(total - sizeof(GcHeader) <= UINT32_MAX);
            h = malloc(total);
            ps_insert(&large_set, (uintptr_t)BODY(h));
            large_push(h);
        }
        gc_young_bytes += total;
        gc_total_bytes += total;
    }
    h->body = (uint32_t)(total - sizeof(GcHeader));
    h->mark = 0;
    h->kind = (uint8_t)kind;
    h->old = 0;
    if (gc_alloc_stats) alloc_record(kind, total);
    alloc_time += (now() - slow_t0) - (gc_time - gc_before);
    return BODY(h);
}

// Mark every line a live object spans (called from `mark_obj` when it first marks
// the object). Large objects aren't block-backed -- skip them.
static void ix_mark_lines(void *body) {
    GcHeader *h = HEADER(body);
    if (sizeof(GcHeader) + h->body > IX_MAX_ALLOC) return; // large object: not block-backed
    IxBlock *b = (IxBlock *)((uintptr_t)h & IX_MASK);
    uint32_t l0 = (uint32_t)(((uintptr_t)h - (uintptr_t)b) / IX_LINE);
    uint32_t l1 = (uint32_t)(((uintptr_t)body + h->body - 1 - (uintptr_t)b) / IX_LINE);
    for (uint32_t i = l0; i <= l1; i++) b->line[i] = 1;
}

// Clear every block's data-line marks so the mark phase rebuilds liveness from
// scratch (header lines stay occupied). Object marks are already 0 at this point
// (cleared for survivors by the previous reclaim; 0 at birth for the rest).
static void ix_reset_lines(void) {
    for (IxBlock *b = ix_blocks; b; b = b->next)
        memset(b->line + b->data_line, 0, IX_LINES - b->data_line);
}

// Reclaim after marking: an unmarked (line==0) line is free -- drop its dead
// objects' start bits so the space can be re-bumped; an occupied line is kept, and
// the marks of the objects starting in it are cleared for the next cycle. Never
// touches a dead object's body -- that is the whole win. Large objects sweep via
// the shared list.
static void ix_reclaim(void) {
    size_t live = 0; // occupied line bytes -- the live set, for the Appel threshold
    ix_recycle = NULL;
    for (IxBlock *b = ix_blocks; b; b = b->next) {
        bool has_free = false;
        for (uint32_t i = b->data_line; i < IX_LINES; i++) {
            if (b->line[i]) {
                live += IX_LINE;
                // A kept line retains any dead objects sharing it (line-granularity
                // floating garbage). Clear a live object's mark for the next cycle,
                // but DROP a dead object's start bit: otherwise a conservative stack
                // word pointing at that retained corpse would pass `is_object` and get
                // traced, following its now-dangling fields into reclaimed memory.
                for (uint32_t g = i * 16u; g < i * 16u + 16u; g++)
                    if ((b->start[g >> 3] >> (g & 7)) & 1) {
                        GcHeader *h = HEADER((void *)((uintptr_t)b + (uintptr_t)g * 8));
                        if (h->mark) h->mark = 0;
                        else b->start[g >> 3] &= (uint8_t) ~(1u << (g & 7));
                    }
            } else {
                has_free = true;
                memset(b->start + i * IX_GBYTES, 0, IX_GBYTES);
            }
        }
        if (has_free) { b->rnext = ix_recycle; ix_recycle = b; } // reusable next epoch
    }
    size_t w = 0; // compact live large objects to the front of the array in place
    for (size_t i = 0; i < gc_large_len; i++) {
        GcHeader *h = gc_large[i];
        if (h->mark) { h->mark = 0; live += sizeof(GcHeader) + h->body; gc_large[w++] = h; }
        else free_object(h);
    }
    gc_large_len = w;
    gc_total_bytes += ix_bytes; // fold this epoch's allocation into the lifetime total
    ix_bytes = 0;               // (the fast path no longer updates gc_total_bytes per object)
    ix_threshold = 2 * live > gc_nursery ? 2 * live : gc_nursery; // grow with the live set
    ix_cur = NULL; ix_ptr = 0; ix_limit = 0; // restart bump allocation from the first block
}

// Conservative membership for the Immix heap: is `w` the body of a live object?
// `w` must be 8-aligned (bodies are), sit in a known block, and carry an
// object-start bit. No slot grid -- the start bitmap is what a variable-size,
// bump-allocated heap uses in place of the slab bitmap.
static bool is_object_immix(uintptr_t w) {
    if (w & 7u) return false;
    IxBlock *b = (IxBlock *)((w - sizeof(GcHeader)) & IX_MASK);
    if (!ps_has(&ix_set, (uintptr_t)b)) return ps_has(&large_set, w);
    // `w` must land in `b`'s data region -- past the header lines and strictly before
    // the block end. A conservative word pointing just past a block otherwise indexes
    // `start[]` out of bounds (its granule `>> 3` reaches 512, one past the array) and
    // could conjure a phantom object at the boundary that the tracer then reads past.
    uintptr_t off = w - (uintptr_t)b;
    if (off < (uintptr_t)b->data_line * IX_LINE || off >= IX_BLOCK) return false;
    return ix_is_start(b, w);
}

// Allocate a header + body, born young. The fast path is the Immix bump: if the
// object fits the current run, claim it with a pointer bump, one object-start bit,
// and a single 8-byte header store -- no call, no collection check (the Appel
// threshold is honoured in `gc_alloc_slow` when a run exhausts, every <=32 KiB).
// Everything else (run refill, large objects, the slab collector, the collection
// trigger) is in the out-of-line `gc_alloc_slow`. Inlined into every fixed-arity
// `mk_*` constructor via `alloc_body`.
static_assert(sizeof(GcHeader) == 8 && offsetof(GcHeader, body) == 0 &&
                  offsetof(GcHeader, kind) == 5,
              "gc_new fast path packs the header into one little-endian 8-byte store");
static inline void *gc_new(size_t body, ObjKind kind) {
    size_t total = (sizeof(GcHeader) + body + 7u) & ~(size_t)7u; // 8-align the bump
    uintptr_t p = ix_ptr;
    if (__builtin_expect(gc_immix && total <= IX_MAX_ALLOC && p + total <= ix_limit, 1)) {
        ix_ptr = p + total;
        GcHeader *h = (GcHeader *)p;
        ix_set_start(ix_cur, (uintptr_t)BODY(h));
        // One store initialises the whole 8-byte header (little-endian): body in
        // bytes 0-3, kind in byte 5, mark/old/pad zero. See the static_assert above.
        *(uint64_t *)h = (uint64_t)(total - sizeof(GcHeader)) | ((uint64_t)(uint8_t)kind << 40);
        ix_bytes += total;
        if (gc_alloc_stats) alloc_record(kind, total);
        return BODY(h);
    }
    return gc_alloc_slow(total, kind);
}

static void gc_report(void) {
    double total = now() - gc_started;
    double mutator = total - gc_time - alloc_time;
    fprintf(stderr,
            "[gc] %lu minor, %lu major; %.1f MB allocated; live old %.1f MB; "
            "nursery %zu KiB\n"
            "[gc] gc %.3fs / total %.3fs -> mutator throughput %.1f%%\n"
            "[time] mutator %.3fs (%.1f%%)  alloc %.3fs (%.1f%%)  gc %.3fs (%.1f%%)\n",
            gc_minor_count, gc_major_count, (gc_total_bytes + ix_bytes) / 1048576.0,
            gc_old_bytes / 1048576.0, gc_nursery >> 10, gc_time, total,
            total > 0 ? 100.0 * (total - gc_time) / total : 100.0,
            mutator, total > 0 ? 100.0 * mutator / total : 0.0,
            alloc_time, total > 0 ? 100.0 * alloc_time / total : 0.0,
            gc_time, total > 0 ? 100.0 * gc_time / total : 0.0);
}

// B5 opportunity report (MARM_ALLOC_STATS): allocation count + volume by kind/arity,
// with the struct-return-State / stack-closure targets (2-tuples, closures, small
// data) called out. The "% bytes" column is share of total allocated volume.
static void alloc_report(void) {
    static const char *names[OBJ_KIND_COUNT] = {"tuple", "closure", "text", "data",
                                                "buffer", "bytes", "mmap", "slice", "float"};
    unsigned long long grand = 0;
    for (int k = 0; k < OBJ_KIND_COUNT; k++)
        for (int a = 0; a <= ALLOC_MAX_ARITY; a++) grand += alloc_hist_b[k][a];
    if (!grand) return;
    fprintf(stderr, "[alloc] by kind/arity (share of %.1f GB total):\n", grand / 1073741824.0);
    unsigned long long tup2 = 0;
    for (int k = 0; k < OBJ_KIND_COUNT; k++) {
        unsigned long long kn = 0, kb = 0;
        for (int a = 0; a <= ALLOC_MAX_ARITY; a++) kn += alloc_hist_n[k][a], kb += alloc_hist_b[k][a];
        if (!kb) continue;
        fprintf(stderr, "[alloc]   %-8s %6.2f%%  (%llu objs)\n", names[k],
                100.0 * (double)kb / (double)grand, kn);
        for (int a = 0; a <= ALLOC_MAX_ARITY; a++)
            if (alloc_hist_n[k][a])
                fprintf(stderr, "[alloc]     arity %2d: %6.2f%%  (%llu)\n", a,
                        100.0 * (double)alloc_hist_b[k][a] / (double)grand, alloc_hist_n[k][a]);
    }
    tup2 = alloc_hist_b[OBJ_TUPLE][2];
    unsigned long long clos = 0, dat = 0;
    for (int a = 0; a <= ALLOC_MAX_ARITY; a++) clos += alloc_hist_b[OBJ_CLOSURE][a], dat += alloc_hist_b[OBJ_DATA][a];
    fprintf(stderr,
            "[alloc] B5 targets: 2-tuples(State pairs)=%.1f%%  closures=%.1f%%  data=%.1f%%  (sum=%.1f%%)\n",
            100.0 * (double)tup2 / (double)grand, 100.0 * (double)clos / (double)grand,
            100.0 * (double)dat / (double)grand,
            100.0 * (double)(tup2 + clos + dat) / (double)grand);
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
    const char *which = getenv("MARM_GC");
    if (which && strcmp(which, "slab") == 0) gc_immix = false;
    if (which && strcmp(which, "immix") == 0) gc_immix = true;
    ix_threshold = gc_nursery; // first immix collection after one nursery of allocation
    if (getenv("MARM_GC_STATS")) atexit(gc_report);
    if (getenv("MARM_ALLOC_STATS")) { gc_alloc_stats = true; atexit(alloc_report); }
    gc_on = true;
}

// Shared builder: allocate a closure with `nfree` inline captures read from the
// (already-started) `va_list`. The per-function `code`/`worker`/`arity` live in the
// shared static `desc`; only the captures are stored here. The captures are read only
// AFTER `gc_new` returns, so across the collection `gc_new` may trigger they are still
// live in the caller's argument area (conservatively scanned) -- as with `mk_tuple`.
static Value mk_closure_dva(const ClosureDesc *desc, size_t nfree, va_list ap) {
    size_t body = sizeof(Closure) + nfree * sizeof(Value);
    Closure *c = gc_new(body, OBJ_CLOSURE);
    c->desc = desc;
    for (size_t i = 0; i < nfree; i++) {
        c->caps[i] = va_arg(ap, Value);
    }
    return VObject(c);
}

Value mk_closure_dn(const ClosureDesc *desc, size_t nfree, ...) {
    va_list ap;
    va_start(ap, nfree);
    Value v = mk_closure_dva(desc, nfree, ap);
    va_end(ap);
    return v;
}

// Compatibility path for callers that pass code/worker/arity directly rather than a
// static descriptor: the runtime builtins and the `FOREIGN_DECL` companions. These
// are few and mostly built once, so a tiny intern cache hands out ONE shared descriptor
// per distinct (code, worker, arity) -- no per-call allocation, no leak. The
// codegen-emitted hot path uses `mk_closure_d*` with its own static descriptors.
static ClosureDesc *intern_desc(Value (*code)(Value, Value),
                                Value (*worker)(Value, Value *), size_t arity) {
    static ClosureDesc *cache[256];
    static size_t ncache = 0;
    for (size_t i = 0; i < ncache; i++)
        if (cache[i]->code == code && cache[i]->worker == worker && cache[i]->arity == arity)
            return cache[i];
    ClosureDesc *d = malloc(sizeof *d); // one per distinct function; never freed
    d->code = code, d->worker = worker, d->arity = arity;
    if (ncache < sizeof cache / sizeof *cache) cache[ncache++] = d;
    return d;
}

Value mk_closure_n(Value (*code)(Value, Value), Value (*worker)(Value, Value *),
                   size_t arity, size_t nfree, ...) {
    va_list ap;
    va_start(ap, nfree);
    Value v = mk_closure_dva(intern_desc(code, worker, arity), nfree, ap);
    va_end(ap);
    return v;
}

Value mk_closure(Value (*code)(Value, Value), size_t nfree, ...) {
    va_list ap;
    va_start(ap, nfree);
    Value v = mk_closure_dva(intern_desc(code, NULL, 1), nfree, ap);
    va_end(ap);
    return v;
}

// Copy `len` bytes into a fresh, collectable Text -- i.e. an OBJ_SLICE over a fresh
// OBJ_BYTES body (Text erases to Bytes erases to a slice). NOT NUL-terminated: Text
// carries an explicit length, and consumers use `slice_len`/`slice_ptr`, never `strlen`.
// `src` stays live across the collection `gc_new` may trigger because it is on the C
// stack (conservatively scanned).
Value mk_textn(const char *src, size_t len) {
    // ONE allocation: an inline-owned OBJ_SLICE -- the Slice header followed by the bytes,
    // with owner == NULL marking "bytes are inline". (The previous form allocated an
    // OBJ_BYTES body plus a separate OBJ_SLICE header -- two objects per computed string.)
    Slice *s = gc_new(sizeof(Slice) + len, OBJ_SLICE);
    s->owner = NULL; // inline-owned: the bytes are this object's own tail
    s->base = (const uint8_t *)(s + 1);
    s->len = len;
    memcpy((char *)(s + 1), src, len); // `src` is a malloc/rodata pointer, not GC memory
    return VObject(s);
}

// Copy a NUL-terminated C string into a collectable string body.
Value mk_text(const char *src) { return mk_textn(src, strlen(src)); }

Value mk_tuple(size_t len, ...) {
    size_t body = sizeof(Tuple) + len * sizeof(Value);
    Tuple *t = gc_new(body, OBJ_TUPLE);
    va_list ap;
    va_start(ap, len);
    for (size_t i = 0; i < len; i++) {
        t->elems[i] = va_arg(ap, Value);
    }
    va_end(ap);
    return VObject(t);
}

Value mk_tuple_uninit(size_t len) {
    size_t body = sizeof(Tuple) + len * sizeof(Value);
    Tuple *t = gc_new(body, OBJ_TUPLE);
    return VObject(t);
}

// ------------------------------------------------------------- flat arrays
// A `Mutable_Array` whose element is a product (a tuple or record -- both are
// OBJ_TUPLE -- at any nesting depth) stores its elements' *leaves* inline, so an
// array of nested products is ONE heap object all the way down instead of the
// array plus a boxed object per element per nesting level (the flat-layout
// north-star: "N nested-product elements = one GC object"). The flat<->canonical
// coercion is localised to get/put, so every caller still only ever sees an
// ordinary boxed value.
//
// Layout: an ordinary OBJ_TUPLE body, so the existing blind even/odd tracer
// walks it unchanged (each stored leaf is one word -- immediate, skipped; or
// pointer, traced). Header words (all immediates, tracer-skipped):
//   [0] count          [1] stride (leaf words per element)   [2] shape_len
//   [3 .. 3+shape_len) shape          then count*stride leaf words.
// The `shape` is a pre-order flattening of the element's product structure: a
// positive entry `k` is a product node of arity `k` (its `k` children follow in
// pre-order); `0` is a leaf (one stored word). It is discovered once from
// element 0 (no type information on the C side); every element of a monomorphic
// array shares it. `flatten`/`unflatten` walk it in lockstep to pack an element
// in / rebuild the canonical nested value out.
//
// Recursion/size guard: a product deeper than FLAT_MAX_DEPTH or wider than
// FLAT_MAX_SHAPE (e.g. a tuple-built recursive structure) falls back to a single
// boxed leaf for the whole element -- the pre-flat representation -- so a
// recursive type is never linearised forever.

#define FLAT_MAX_SHAPE 128
#define FLAT_MAX_DEPTH 16
#define FLAT_ARRAY_CTAG 1 // `ctag` marker distinguishing a flat-array OBJ_TUPLE from a product
#define FLAT_MAX_FIELDS 64 // max constructor fields rebuilt on the C stack in unflatten
// A shape entry is: 0 = leaf (one stored word); k>0 = product/variant of arity k
// (its k child nodes follow in pre-order); SHAPE_SUM = an inlined sum, encoded
// `[SHAPE_SUM, pad, nvariants, <variant nodes>]` where pad is the union payload
// width (max variant leaves) and each variant node is `[m, <m field shapes>]`
// (m = that constructor's field count). A sum element occupies `1 + pad` stored
// words: [tag, active variant's leaves, zero-padding]. Sum nodes are emitted only
// by codegen from the element TYPE (via a shaped array), never by element-0
// discovery (`build_shape`), which cannot see a sum's other variants.
#define SHAPE_SUM (-1)
// A two-constructor sum with one nullary constructor and one unary payload
// constructor can consume a proven zero niche in the payload. Encoding:
// `[SHAPE_NICHE_SUM, niche_tag, payload_tag, niche_word_offset,
//   payload_field_count, payload_field_shapes...]`.
// It occupies exactly the payload width: the nullary value is all zeroes and the
// payload value is representation-transparent.
#define SHAPE_NICHE_SUM (-2)

// Number of int64 entries the shape node at `i` spans (pre-order). A variant node
// `[m, ...]` shares the product/leaf span logic (span of `[0]` and of an empty
// variant `[0]` coincide), so only the sum header needs special handling.
static size_t shape_span(const int64_t *shape, size_t i) {
    int64_t node = shape[i];
    if (node >= 0) { // leaf (0) or product/variant of arity `node`
        size_t span = 1, c = i + 1;
        for (int64_t k = 0; k < node; k++) { size_t s = shape_span(shape, c); c += s; span += s; }
        return span;
    }
    if (node == SHAPE_NICHE_SUM) return 4 + shape_span(shape, i + 4);
    int64_t nv = shape[i + 2]; // sum: [SHAPE_SUM, pad, nvariants] then each variant node
    size_t span = 3, c = i + 3;
    for (int64_t k = 0; k < nv; k++) { size_t s = shape_span(shape, c); c += s; span += s; }
    return span;
}

// Pre-order shape of a value: append product/leaf entries to `shape`, return the
// leaf count. `*ok` is cleared (and expansion stops) past the size/depth guard,
// so the caller falls back to treating the whole element as one boxed leaf.
// `MARM_NOFLAT` forces the boxed leaf (stride 1) for A/B measurement.
static size_t build_shape(Value v, int64_t *shape, size_t *slen, int depth, bool *ok) {
    static int noflat = -1;
    if (noflat < 0) noflat = getenv("MARM_NOFLAT") != NULL;
    if (*slen >= FLAT_MAX_SHAPE) { *ok = false; return 1; }
    // Recurse only into a genuine product tuple: a non-zero pointer to an OBJ_TUPLE
    // that is NOT itself a flat array (a nested flat array is opaque -- one leaf). The
    // `v.w != 0` guard rejects a zero word (e.g. a sum element's inline padding) that
    // would otherwise be chased as a pointer and fault.
    if (!noflat && depth <= FLAT_MAX_DEPTH && v.w != 0 && !(v.w & IMM_TAG) &&
        HEADER(as_ptr(v))->kind == OBJ_TUPLE && HEADER(as_ptr(v))->ctag != FLAT_ARRAY_CTAG) {
        Tuple *t = as_tuple(v);
        size_t k = HEADER(t)->body / sizeof(Value);
        shape[(*slen)++] = (int64_t)k; // product node of arity k
        size_t leaves = 0;
        for (size_t i = 0; i < k && *ok; i++) {
            leaves += build_shape(t->elems[i], shape, slen, depth + 1, ok);
        }
        return leaves;
    }
    shape[(*slen)++] = 0; // leaf
    return 1;
}

static size_t shape_leaves(const int64_t *shape, size_t *i);

// Pack `v`'s leaves into `dest` in shape order (advancing both cursors). A sum
// node writes [tag, active variant's leaves, zero-padding to the union payload];
// the padding keeps the blind even/odd tracer correct (0 is skipped -- DD3).
static void flatten(Value v, const int64_t *shape, size_t *si, Value *dest, size_t *di) {
    int64_t node = shape[*si];
    if (node == 0) { // leaf: one stored word
        (*si)++;
        dest[(*di)++] = v;
        return;
    }
    if (node > 0) { // product/record: `v` is a Tuple, flatten its fields in order
        (*si)++;
        Tuple *t = as_tuple(v);
        for (int64_t i = 0; i < node; i++) flatten(t->elems[i], shape, si, dest, di);
        return;
    }
    if (node == SHAPE_NICHE_SUM) {
        size_t node_i = *si;
        uint64_t tag = data_tag(v);
        uint64_t niche_tag = (uint64_t)shape[node_i + 1];
        uint64_t payload_tag = (uint64_t)shape[node_i + 2];
        size_t payload_i = node_i + 4;
        size_t end_i = node_i + shape_span(shape, node_i);
        if (tag == niche_tag) {
            size_t cursor = payload_i;
            size_t words = shape_leaves(shape, &cursor);
            for (size_t i = 0; i < words; i++) dest[(*di)++] = (Value){0};
        } else {
            int64_t fields = shape[payload_i++];
            if (tag != payload_tag || data_len(v) != (size_t)fields) match_fail();
            for (int64_t i = 0; i < fields; i++)
                flatten(data_field(v, (size_t)i), shape, &payload_i, dest, di);
        }
        *si = end_i;
        return;
    }
    // sum: `v` is a Data (tag in the header, fields inline).
    size_t node_i = *si;
    int64_t pad = shape[node_i + 1];
    uint64_t tag = data_tag(v);
    dest[(*di)++] = VInt((int64_t)tag);
    size_t c = node_i + 3; // walk past earlier variant nodes to the active one
    for (uint64_t k = 0; k < tag; k++) c += shape_span(shape, c);
    int64_t m = shape[c]; // active variant's field count; its field shapes follow
    size_t vi = c + 1, di0 = *di;
    for (int64_t i = 0; i < m; i++) flatten(data_field(v, i), shape, &vi, dest, di);
    for (size_t p = *di - di0; p < (size_t)pad; p++) dest[(*di)++] = (Value){0}; // zero-pad
    *si = node_i + shape_span(shape, node_i);
}

// Rebuild the canonical (nested) value from `src`'s leaves in shape order. A
// product node allocates its tuple zeroed and fills field-by-field: the
// half-built tuple is a live stack root and its unset fields are 0 (tracer-
// skipped), so a GC during a later field's rebuild is safe; the GC is non-moving
// so `src` (into the rooted array) stays valid.
static Value unflatten(const int64_t *shape, size_t *si, const Value *src, size_t *sri) {
    int64_t node = shape[*si];
    if (node == 0) {
        (*si)++;
        return src[(*sri)++];
    }
    if (node > 0) {
        (*si)++;
        size_t body = sizeof(Tuple) + (size_t)node * sizeof(Value);
        Tuple *t = gc_new(body, OBJ_TUPLE);
        memset(t->elems, 0, (size_t)node * sizeof(Value));
        Value out = VObject(t);
        for (int64_t i = 0; i < node; i++) {
            Value child = unflatten(shape, si, src, sri);
            as_tuple(out)->elems[i] = child; // re-read: `out` may have survived a GC
        }
        return out;
    }
    if (node == SHAPE_NICHE_SUM) {
        size_t node_i = *si;
        uint64_t niche_tag = (uint64_t)shape[node_i + 1];
        uint64_t payload_tag = (uint64_t)shape[node_i + 2];
        size_t niche_offset = (size_t)shape[node_i + 3];
        size_t payload_i = node_i + 4;
        size_t cursor = payload_i;
        size_t words = shape_leaves(shape, &cursor);
        size_t payload0 = *sri;
        Value out;
        if (src[payload0 + niche_offset].w == 0) {
            out = mk_data_inline(VInt((int64_t)niche_tag), 0, NULL);
        } else {
            int64_t field_count = shape[payload_i++];
            Value fields[FLAT_MAX_FIELDS];
            for (int64_t i = 0; i < field_count; i++)
                fields[i] = unflatten(shape, &payload_i, src, sri);
            out = mk_data_inline(VInt((int64_t)payload_tag), (size_t)field_count, fields);
        }
        *sri = payload0 + words;
        *si = node_i + shape_span(shape, node_i);
        return out;
    }
    // sum: read the tag word, rebuild the active variant's boxed Data. The fields
    // build into a C-stack array (each is a conservative root while later fields'
    // rebuilds may GC); `src` points into the rooted, non-moving array, so it stays
    // valid across those allocations.
    size_t node_i = *si;
    int64_t pad = shape[node_i + 1];
    uint64_t tag = (uint64_t)as_int(src[*sri]);
    (*sri)++;
    size_t payload0 = *sri;
    size_t c = node_i + 3;
    for (uint64_t k = 0; k < tag; k++) c += shape_span(shape, c);
    int64_t m = shape[c];
    size_t vi = c + 1;
    Value fields[FLAT_MAX_FIELDS];
    for (int64_t i = 0; i < m; i++) fields[i] = unflatten(shape, &vi, src, sri);
    Value out = mk_data_inline(VInt((int64_t)tag), (size_t)m, fields);
    *sri = payload0 + (size_t)pad; // skip the union payload (active leaves + padding)
    *si = node_i + shape_span(shape, node_i);
    return out;
}

// Copy the array's shape into `buf` (small; <= FLAT_MAX_SHAPE); returns its len.
static size_t read_shape(Value arr, int64_t *buf) {
    Tuple *t = as_tuple(arr);
    size_t slen = (size_t)as_int(t->elems[2]);
    for (size_t i = 0; i < slen; i++) buf[i] = as_int(t->elems[3 + i]);
    return slen;
}

static size_t flat_elem_base(Value arr) { return 3 + (size_t)as_int(as_tuple(arr)->elems[2]); }

// Allocate a zeroed flat array with its header + shape filled in. Zeroing is
// mandatory: gc_new does not zero, the tracer trusts every even word, and
// generation fills element-by-element with GC-triggering callbacks in between --
// a garbage word would be chased as a pointer; a zeroed word is 0, which
// mark_value skips (see notes/flat-layout.md DD3).
static Value mk_flat_array(size_t count, size_t stride, const int64_t *shape, size_t slen) {
    if (stride == 0) stride = 1;
    size_t words = 3 + slen + count * stride;
    size_t body = sizeof(Tuple) + words * sizeof(Value);
    Tuple *t = gc_new(body, OBJ_TUPLE);
    memset(t->elems, 0, words * sizeof(Value));
    // Mark this OBJ_TUPLE as a flat array (the `ctag` header byte is otherwise unused
    // for tuples). A flat array's body is `[count, stride, shape...]` + packed leaves,
    // NOT a plain product, so `build_shape` must treat a NESTED flat array as one
    // opaque leaf rather than recursing into its header/padding words (which it would
    // misread -- and a zero-padding word would fault as a bogus pointer).
    HEADER(t)->ctag = FLAT_ARRAY_CTAG;
    t->elems[0] = VInt((int64_t)count);
    t->elems[1] = VInt((int64_t)stride);
    t->elems[2] = VInt((int64_t)slen);
    for (size_t i = 0; i < slen; i++) t->elems[3 + i] = VInt(shape[i]);
    return VObject(t);
}

size_t flat_array_count(Value arr) { return (size_t)as_int(as_tuple(arr)->elems[0]); }

// Store element `i` in place (no boxing, no allocation), packing its leaves.
void flat_array_set(Value arr, size_t i, Value elt) {
    int64_t shape[FLAT_MAX_SHAPE];
    size_t slen = read_shape(arr, shape);
    Tuple *t = as_tuple(arr);
    size_t stride = (size_t)as_int(t->elems[1]);
    Value *slot = &t->elems[flat_elem_base(arr) + i * stride];
    size_t si = 0, di = 0;
    flatten(elt, shape, &si, slot, &di);
    gc_remember_object(t);
}

// Read element `i` back out as a canonical (nested) value. `arr` is a live root
// on the caller's stack across the rebuild allocation.
Value flat_array_get(Value arr, size_t i) {
    int64_t shape[FLAT_MAX_SHAPE];
    read_shape(arr, shape);
    size_t stride = (size_t)as_int(as_tuple(arr)->elems[1]);
    size_t base = flat_elem_base(arr) + i * stride;
    size_t si = 0, sri = base;
    return unflatten(shape, &si, as_tuple(arr)->elems, &sri);
}

// Decode only the sole field of a top-level niche-sum payload. This is the
// representation-level counterpart of matching `This x` when the caller has
// already established the occupied-slot invariant: a leaf payload is returned
// directly, while a product payload rebuilds only that product -- never `This`.
Value flat_array_get_niche_payload_unchecked(Value arr, size_t i) {
    int64_t shape[FLAT_MAX_SHAPE];
    size_t slen = read_shape(arr, shape);
    if (slen < 6 || shape[0] != SHAPE_NICHE_SUM || shape[4] != 1) match_fail();

    size_t stride = (size_t)as_int(as_tuple(arr)->elems[1]);
    size_t source_i = flat_elem_base(arr) + i * stride;
    size_t shape_i = 5; // niche header (4), payload field count (1), then field 0
    return unflatten(shape, &shape_i, as_tuple(arr)->elems, &source_i);
}

Value flat_array_get_word(Value arr, size_t i, size_t word_offset) {
    Tuple *t = as_tuple(arr);
    size_t stride = (size_t)as_int(t->elems[1]);
    return t->elems[flat_elem_base(arr) + i * stride + word_offset];
}

void flat_array_set_word(Value arr, size_t i, size_t word_offset, Value value) {
    Tuple *t = as_tuple(arr);
    size_t stride = (size_t)as_int(t->elems[1]);
    t->elems[flat_elem_base(arr) + i * stride + word_offset] = value;
    gc_remember_object(t);
}

void flat_array_set_word_immediate(Value arr, size_t i, size_t word_offset,
                                   Value value) {
    Tuple *t = as_tuple(arr);
    size_t stride = (size_t)as_int(t->elems[1]);
    t->elems[flat_elem_base(arr) + i * stride + word_offset] = value;
}

// Store element `i`, returning the previous element boxed out. The box-out runs
// before the overwrite; `elt` is a live root on the stack across it.
Value flat_array_put(Value arr, size_t i, Value elt) {
    Value prev = flat_array_get(arr, i);
    flat_array_set(arr, i, elt);
    return prev;
}

// Copy packed elements directly between arrays. The language-level element type
// guarantees equal layouts; keep a runtime check here because a mismatched stride
// would otherwise turn a type/layout bug into heap corruption. `memmove` also makes
// copying within one array well-defined for overlapping ranges.
void flat_array_copy(Value source, size_t source_index, Value target,
                     size_t target_index, size_t count) {
    Tuple *src = as_tuple(source);
    Tuple *dst = as_tuple(target);
    size_t src_stride = (size_t)as_int(src->elems[1]);
    size_t dst_stride = (size_t)as_int(dst->elems[1]);
    size_t src_slen = (size_t)as_int(src->elems[2]);
    size_t dst_slen = (size_t)as_int(dst->elems[2]);

    if (src_stride != dst_stride || src_slen != dst_slen ||
        memcmp(&src->elems[3], &dst->elems[3], src_slen * sizeof(Value)) != 0) {
        fprintf(stderr, "flat_array_copy: incompatible element layouts\n");
        abort();
    }

    Value *src_words = &src->elems[flat_elem_base(source) + source_index * src_stride];
    Value *dst_words = &dst->elems[flat_elem_base(target) + target_index * dst_stride];
    memmove(dst_words, src_words, count * src_stride * sizeof(Value));
    if (count != 0) gc_remember_object(dst);
}

// Grow without boxing the old prefix or invoking a generator for every slot.
// The allocation is already zeroed for the tracer. Consequently an all-zero
// packed fill (notably Nope in a niche-layout Perhaps) needs no suffix writes.
Value flat_array_grow_with(Value source, size_t new_count, Value fill) {
    Tuple *src = as_tuple(source);
    size_t old_count = flat_array_count(source);
    if (new_count < old_count) {
        fprintf(stderr, "flat_array_grow_with: new length is smaller than source\n");
        abort();
    }

    size_t stride = (size_t)as_int(src->elems[1]);
    int64_t shape[FLAT_MAX_SHAPE];
    size_t slen = read_shape(source, shape);
    Value target = mk_flat_array(new_count, stride, shape, slen);

    Tuple *dst = as_tuple(target); // the collector is non-moving
    size_t src_base = flat_elem_base(source);
    size_t dst_base = flat_elem_base(target);
    memmove(&dst->elems[dst_base], &src->elems[src_base],
            old_count * stride * sizeof(Value));

    if (new_count > old_count) {
        Value *packed_fill = &dst->elems[dst_base + old_count * stride];
        size_t si = 0, di = 0;
        flatten(fill, shape, &si, packed_fill, &di);

        bool all_zero = true;
        for (size_t word = 0; word < stride; word++)
            all_zero &= packed_fill[word].w == 0;

        if (!all_zero) {
            // Double the initialized suffix each time. This copies the same
            // number of words as a slot loop but makes only O(log n) memcpy calls.
            size_t filled = 1;
            size_t suffix_count = new_count - old_count;
            while (filled < suffix_count) {
                size_t chunk = filled < suffix_count - filled
                    ? filled : suffix_count - filled;
                memcpy(packed_fill + filled * stride, packed_fill,
                       chunk * stride * sizeof(Value));
                filled += chunk;
            }
        }
    }

    if (new_count != 0) gc_remember_object(dst);
    return target;
}

// Build a flat array from `n` already-evaluated element values (a readonly
// `[...]` literal). Shape from element 0; the `elems` block is a live stack root
// across the alloc. Mirrors `flat_generate` without the per-index callback.
Value mk_flat_array_from(size_t n, Value *elems) {
    int64_t shape[FLAT_MAX_SHAPE];
    if (n == 0) {
        shape[0] = 0;
        return mk_flat_array(0, 1, shape, 1);
    }
    size_t slen = 0;
    bool ok = true;
    size_t stride = build_shape(elems[0], shape, &slen, 0, &ok);
    if (!ok) {
        slen = 0;
        shape[slen++] = 0;
        stride = 1;
    }
    Value arr = mk_flat_array(n, stride, shape, slen); // may GC; elems[] rooted on stack
    for (size_t i = 0; i < n; i++) flat_array_set(arr, i, elems[i]);
    return arr;
}

// Stored-word count (stride contribution) of the shape node at `*i`, advancing
// `*i` past it. A sum node contributes `1 + pad` (tag + union payload).
static size_t shape_leaves(const int64_t *shape, size_t *i) {
    int64_t node = shape[*i];
    if (node == 0) { (*i)++; return 1; }
    if (node > 0) {
        (*i)++;
        size_t sum = 0;
        for (int64_t k = 0; k < node; k++) sum += shape_leaves(shape, i);
        return sum;
    }
    if (node == SHAPE_NICHE_SUM) {
        *i += 4;
        return shape_leaves(shape, i);
    }
    size_t pad = (size_t)shape[*i + 1];
    *i += shape_span(shape, *i);
    return 1 + pad;
}

// Build a flat array from `n` evaluated elements using a caller-supplied,
// type-driven shape (codegen emits it from the element type). Unlike
// `mk_flat_array_from`, the shape may contain sum nodes: element-0 discovery
// cannot see a sum's other variants, so a sum element's shape MUST come from the
// type. `elems` is a live stack root across the (GC-triggering) allocation.
Value mk_flat_array_from_shaped(size_t n, Value *elems, const int64_t *shape, size_t slen) {
    size_t i0 = 0;
    size_t stride = shape_leaves(shape, &i0);
    Value arr = mk_flat_array(n, stride, shape, slen);
    for (size_t i = 0; i < n; i++) flat_array_set(arr, i, elems[i]);
    return arr;
}

// Build a flat array of `length` elements, each `apply(mk_element, i)`. The
// element shape is taken from element 0; an empty array defaults to one leaf.
Value flat_generate(int64_t length, Value mk_element) {
    int64_t shape[FLAT_MAX_SHAPE];
    if (length <= 0) {
        shape[0] = 0;
        return mk_flat_array(0, 1, shape, 1);
    }
    Value e0 = apply(mk_element, VInt(0)); // may GC; mk_element rooted on stack
    size_t slen = 0;
    bool ok = true;
    size_t stride = build_shape(e0, shape, &slen, 0, &ok);
    if (!ok) { // too deep/wide: fall back to one boxed leaf per element
        slen = 0;
        shape[slen++] = 0;
        stride = 1;
    }
    Value arr = mk_flat_array((size_t)length, stride, shape, slen); // may GC; e0 rooted
    flat_array_set(arr, 0, e0);
    for (int64_t i = 1; i < length; i++) {
        Value ei = apply(mk_element, VInt(i)); // may GC; arr rooted on stack
        flat_array_set(arr, (size_t)i, ei);
    }
    return arr;
}

// Like `flat_generate` but with a caller-supplied, type-driven element shape (from
// the `Memory_Layout` dictionary), so a sum element packs inline instead of staying
// a boxed pointer. Unlike `flat_generate`'s element-0 discovery, this shape covers
// every variant of the element type, so a later `flat_array_put` of any variant is
// sound. Each `apply(mk_element, i)` may GC; `arr` is rooted on the stack across it.
Value flat_generate_shaped(int64_t length, Value mk_element, const int64_t *shape, size_t slen) {
    size_t i0 = 0;
    size_t stride = shape_leaves(shape, &i0);
    if (length <= 0) return mk_flat_array(0, stride, shape, slen);
    Value arr = mk_flat_array((size_t)length, stride, shape, slen);
    for (int64_t i = 0; i < length; i++) {
        Value ei = apply(mk_element, VInt(i));
        flat_array_set(arr, (size_t)i, ei);
    }
    return arr;
}

// Consume exactly `length` elements from an Enumeratee state. `next` returns
// `Perhaps (element, state)`: This has constructor tag 1 and its sole field is
// the pair. The witness is responsible for supplying enough elements; failure
// before the promised size is an invalid witness, just like an out-of-range
// index from the indexed enumerator.
Value flat_from_enumerator_shaped(int64_t length, Value enumeration, Value next,
                                  const int64_t *shape, size_t slen) {
    size_t i0 = 0;
    size_t element_stride = shape_leaves(shape, &i0);
    if (length <= 0) return mk_flat_array(0, element_stride, shape, slen);

    Value arr = mk_flat_array((size_t)length, element_stride, shape, slen);
    for (int64_t produced = 0; produced < length; produced++) {
        Value step = apply(next, enumeration);
        if (data_tag(step) != 1) match_fail();
        Value pair = data_field(step, 0);
        Value indexed_element = proj(pair, 0);
        enumeration = proj(pair, 1);
        int64_t index = as_int(proj(indexed_element, 0));
        Value element = proj(indexed_element, 1);
        flat_array_set(arr, (size_t)index, element);
    }
    return arr;
}

Value flat_from_enumerator(int64_t length, Value enumeration, Value next) {
    int64_t shape[FLAT_MAX_SHAPE];
    if (length <= 0) {
        shape[0] = 0;
        return mk_flat_array(0, 1, shape, 1);
    }

    Value first_step = apply(next, enumeration);
    if (data_tag(first_step) != 1) match_fail();
    Value first_pair = data_field(first_step, 0);
    Value first_indexed_element = proj(first_pair, 0);
    int64_t first_index = as_int(proj(first_indexed_element, 0));
    Value first_element = proj(first_indexed_element, 1);
    enumeration = proj(first_pair, 1);

    size_t slen = 0;
    bool ok = true;
    size_t element_stride = build_shape(first_element, shape, &slen, 0, &ok);
    if (!ok) {
        slen = 0;
        shape[slen++] = 0;
        element_stride = 1;
    }

    Value arr = mk_flat_array((size_t)length, element_stride, shape, slen);
    flat_array_set(arr, (size_t)first_index, first_element);
    for (int64_t produced = 1; produced < length; produced++) {
        Value step = apply(next, enumeration);
        if (data_tag(step) != 1) match_fail();
        Value pair = data_field(step, 0);
        Value indexed_element = proj(pair, 0);
        enumeration = proj(pair, 1);
        int64_t index = as_int(proj(indexed_element, 0));
        Value element = proj(indexed_element, 1);
        flat_array_set(arr, (size_t)index, element);
    }
    return arr;
}

// Rebuild a boxed constructor from an INLINED sum's region (copy-out): `tag_imm`
// is the inline tag (an immediate VInt), `payload_words` the union payload width,
// `src` the payload words (active variant's fields, then zeroed padding). The
// result is a max-payload OBJ_DATA -- the padding fields stay 0 (tracer-skipped)
// and are never read by the active variant's pattern. `src` points into a live,
// non-moving object, so it survives the alloc.
Value mk_data_inline(Value tag_imm, size_t payload_words, const Value *src) {
    Data *d = gc_new(sizeof(Data) + payload_words * sizeof(Value), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)as_int(tag_imm);
    if (payload_words) memcpy(d->fields, src, payload_words * sizeof(Value));
    return VObject(d);
}

Value mk_data(uint64_t tag, size_t nfields, ...) {
    size_t body = sizeof(Data) + nfields * sizeof(Value);
    Data *d = gc_new(body, OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag;
    va_list ap;
    va_start(ap, nfields);
    for (size_t i = 0; i < nfields; i++) {
        d->fields[i] = va_arg(ap, Value);
    }
    va_end(ap);
    return VObject(d);
}

// Box a double: an OBJ_FLOAT leaf whose body is exactly the 8-byte double. Every
// computed Float allocates one (a 64-bit IEEE-754 value cannot live in the tagged
// word); `as_float` reads it back. Literals use the immortal STATIC_FLOAT box instead.
Value mk_float(double x) {
    double *p = gc_new(sizeof(double), OBJ_FLOAT);
    *p = x;
    return VObject(p);
}

// ---------------------------------------------- fixed-arity constructors
// Codegen knows a constructor/tuple/closure's field count statically, so for the
// common small arities it emits these instead of the variadic `mk_*` above. That
// drops the whole `va_list` setup + field-copy loop (measured ~14% of allocation
// cost on a cons-heavy loop), and -- since `alloc_body` and the inline-fast `gc_new`
// fold in -- turns a fixed-arity `mk_*` into a straight-line bump. No `gc_reserve`
// call: the collection trigger now lives in `gc_new`'s cold `gc_alloc_slow`, which
// runs whenever a bump run exhausts. GC safety is unchanged: the field/capture
// arguments live in this frame across any collection, and the collector scans the
// stack (and setjmp-spilled registers) conservatively.
static inline void *alloc_body(size_t body, ObjKind kind) {
    return gc_new(body, kind);
}

Value mk_data0(uint64_t tag) {
    Data *d = alloc_body(sizeof(Data), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag;
    return VObject(d);
}
Value mk_data1(uint64_t tag, Value f0) {
    Data *d = alloc_body(sizeof(Data) + 1 * sizeof(Value), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag, d->fields[0] = f0;
    return VObject(d);
}
Value mk_data2(uint64_t tag, Value f0, Value f1) {
    Data *d = alloc_body(sizeof(Data) + 2 * sizeof(Value), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag, d->fields[0] = f0, d->fields[1] = f1;
    return VObject(d);
}
Value mk_data3(uint64_t tag, Value f0, Value f1, Value f2) {
    Data *d = alloc_body(sizeof(Data) + 3 * sizeof(Value), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag, d->fields[0] = f0, d->fields[1] = f1, d->fields[2] = f2;
    return VObject(d);
}
Value mk_data4(uint64_t tag, Value f0, Value f1, Value f2, Value f3) {
    Data *d = alloc_body(sizeof(Data) + 4 * sizeof(Value), OBJ_DATA);
    HEADER(d)->ctag = (uint8_t)tag, d->fields[0] = f0, d->fields[1] = f1, d->fields[2] = f2, d->fields[3] = f3;
    return VObject(d);
}

Value mk_tuple0(void) {
    Tuple *t = alloc_body(sizeof(Tuple), OBJ_TUPLE);
    return VObject(t);
}
Value mk_tuple1(Value e0) {
    Tuple *t = alloc_body(sizeof(Tuple) + 1 * sizeof(Value), OBJ_TUPLE);
    t->elems[0] = e0;
    return VObject(t);
}
Value mk_tuple2(Value e0, Value e1) {
    Tuple *t = alloc_body(sizeof(Tuple) + 2 * sizeof(Value), OBJ_TUPLE);
    t->elems[0] = e0, t->elems[1] = e1;
    return VObject(t);
}
Value mk_tuple3(Value e0, Value e1, Value e2) {
    Tuple *t = alloc_body(sizeof(Tuple) + 3 * sizeof(Value), OBJ_TUPLE);
    t->elems[0] = e0, t->elems[1] = e1, t->elems[2] = e2;
    return VObject(t);
}
Value mk_tuple4(Value e0, Value e1, Value e2, Value e3) {
    Tuple *t = alloc_body(sizeof(Tuple) + 4 * sizeof(Value), OBJ_TUPLE);
    t->elems[0] = e0, t->elems[1] = e1, t->elems[2] = e2, t->elems[3] = e3;
    return VObject(t);
}

// Closure builders. The per-function `code`/`worker`/`arity` come from the shared
// static `desc` (codegen emits one per closure site); only the captures are stored
// in the heap object, so a closure body is `sizeof(Closure)` (one pointer) + captures.
Value mk_closure_d0(const ClosureDesc *desc) {
    Closure *c = alloc_body(sizeof(Closure), OBJ_CLOSURE);
    c->desc = desc;
    return VObject(c);
}
Value mk_closure_d1(const ClosureDesc *desc, Value c0) {
    Closure *c = alloc_body(sizeof(Closure) + 1 * sizeof(Value), OBJ_CLOSURE);
    c->desc = desc, c->caps[0] = c0;
    return VObject(c);
}
Value mk_closure_d2(const ClosureDesc *desc, Value c0, Value c1) {
    Closure *c = alloc_body(sizeof(Closure) + 2 * sizeof(Value), OBJ_CLOSURE);
    c->desc = desc, c->caps[0] = c0, c->caps[1] = c1;
    return VObject(c);
}
Value mk_closure_d3(const ClosureDesc *desc, Value c0, Value c1, Value c2) {
    Closure *c = alloc_body(sizeof(Closure) + 3 * sizeof(Value), OBJ_CLOSURE);
    c->desc = desc, c->caps[0] = c0, c->caps[1] = c1, c->caps[2] = c2;
    return VObject(c);
}
Value mk_closure_d4(const ClosureDesc *desc, Value c0, Value c1, Value c2, Value c3) {
    Closure *c = alloc_body(sizeof(Closure) + 4 * sizeof(Value), OBJ_CLOSURE);
    c->desc = desc, c->caps[0] = c0, c->caps[1] = c1, c->caps[2] = c2, c->caps[3] = c3;
    return VObject(c);
}

// Field count of a live constructor value, recovered from its heap header's body
// size (the count is not stored in the object itself).
size_t data_len(Value v) {
    return (HEADER(as_ptr(v))->body - sizeof(Data)) / sizeof(Value);
}

// Element count of a tuple (also the backing of Array), recovered from the header
// body size: a tuple body is exactly `n * sizeof(Value)` (no stored length).
size_t tuple_len(Value v) {
    return HEADER(as_ptr(v))->body / sizeof(Value);
}

// ----------------------------------------------------------------- byte buffers
Value mk_buffer(size_t cap) {
    if (cap == 0) cap = 16;
    void *body = gc_new(cap, OBJ_BYTES); // stays live on the stack across the next gc_new
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
        void *nbody = gc_new(ncap, OBJ_BYTES);
        b = as_ptr(bv);
        memcpy(nbody, b->bytes, b->len);
        b->bytes = nbody;
        b->cap = ncap;
        gc_remember_object(b); // old handle -> young body: record for the minor barrier
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

Value mk_slice_at(void *owner, const uint8_t *base, size_t len) {
    // `owner` is a body pointer; it sits on the stack (conservatively scanned), so
    // it survives the collection `gc_new` may trigger. `base` is an interior pointer
    // into whatever `owner` keeps alive -- safe only because the collector never
    // moves objects.
    Slice *s = gc_new(sizeof(Slice), OBJ_SLICE);
    s->owner = owner;
    s->base = base;
    s->len = len;
    return VObject(s);
}

// Resolve `owner + offset` to a read pointer ONCE, here, rather than on every byte
// read. `owner` is an OBJ_BYTES body or an OBJ_MMAP handle; inline-owned slices are
// built by `mk_textn`, and sub-views by `slice_sub`, both of which know their base
// directly and call `mk_slice_at`.
Value mk_slice(void *owner, size_t offset, size_t len) {
    const uint8_t *base = HEADER(owner)->kind == OBJ_BYTES
                              ? (const uint8_t *)owner + offset
                              : ((Mmap *)owner)->region + offset;
    return mk_slice_at(owner, base, len);
}

// Hand the buffer's body to a Slice, then reseed the handle with a fresh empty
// body so it no longer aliases the bytes it gave away.
Value buffer_move(Value bv) {
    Buffer *b = as_ptr(bv);
    size_t len = b->len;
    void *body = b->bytes; // handed off below; stays live on the stack meanwhile
    void *fresh = gc_new(16, OBJ_BYTES);
    b = as_ptr(bv);
    b->bytes = fresh;
    b->len = 0;
    b->cap = 16;
    gc_remember_object(b); // old handle -> young body: record for the minor barrier
    return mk_slice(body, 0, len);
}

Value buffer_copy(Value bv) {
    size_t n = ((Buffer *)as_ptr(bv))->len;
    void *body = gc_new(n ? n : 1, OBJ_BYTES);
    Buffer *b = as_ptr(bv); // re-fetch after the possible collection
    memcpy(body, b->bytes, n);
    return mk_slice(body, 0, n);
}

// `slice_base`, `slice_len`, `slice_ptr` and `slice_get_u8` are now `static inline`
// in gc.h -- each is one load off the resolved `base`, so they fold into their callers
// across translation units. The old form re-derived the address on EVERY byte (load the
// owner's GcHeader, dispatch on its kind, recurse for a borrowed sub-view), which made
// `Bytes.get_u8` three calls deep and could not inline at all because of the recursion.

// Copy a Text/Bytes slice into a caller buffer as a NUL-terminated C string, for the C
// APIs that need one (file paths, strtol). Text is length-prefixed, not NUL-terminated,
// so this is the explicit bridge. Returns false (writing nothing) if it does not fit.
bool text_to_cstr(Value sv, char *buf, size_t cap) {
    size_t n = slice_len(sv);
    if (n + 1 > cap) return false;
    memcpy(buf, slice_ptr(sv), n);
    buf[n] = '\0';
    return true;
}

// Index of the first `byte` at or after `from`, or -1. This is `memchr`, which scans
// word-at-a-time and vectorises; the equivalent Marmelade loop reads one byte per
// iteration through a predicate call. `from` past the end is not an error -- it simply
// finds nothing, which is what lets the caller drive a parse loop without a separate
// bounds check on every row.
int64_t slice_position(Value sv, int64_t from, int64_t byte) {
    const Slice *s = as_ptr(sv);
    if (from < 0 || (size_t)from >= s->len) return -1;
    const uint8_t *hit =
        memchr(s->base + from, (int)(uint8_t)byte, s->len - (size_t)from);
    return hit ? (int64_t)(hit - s->base) : -1;
}

Value slice_sub(Value sv, size_t off, size_t len) {
    Slice *s = as_ptr(sv);
    // The base is already resolved, so a sub-view is just base + off -- no owner
    // dispatch, and correct for every ownership kind including inline-owned (which
    // the old `mk_slice(s->owner, ...)` got WRONG: it passed the parent's NULL owner
    // along, so the sub-view claimed its bytes lived behind its own empty header).
    //
    // An inline-owned parent IS the object holding the bytes, so the sub-view must
    // borrow it as its liveness link or the parent could be collected out from under
    // it. That link is never followed for addressing.
    void *owner = s->owner ? s->owner : (void *)s;
    return mk_slice_at(owner, s->base + off, len);
}

#define SLICE_GET_LE(NAME, TYPE, N)                                                    \
    TYPE NAME(Value sv, size_t off) {                                                  \
        const uint8_t *p = slice_ptr(sv) + off;                                    \
        uint64_t v = 0;                                                                \
        for (size_t k = 0; k < (N); k++) v |= (uint64_t)p[k] << (8 * k);               \
        return (TYPE)v;                                                                \
    }
#define SLICE_GET_BE(NAME, TYPE, N)                                                    \
    TYPE NAME(Value sv, size_t off) {                                                  \
        const uint8_t *p = slice_ptr(sv) + off;                                    \
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

// ------------------------------------------------------------- UTF-8 validation
// Validate a byte range as well-formed UTF-8 (RFC 3629). Two paths, chosen per
// character boundary:
//   * ASCII fast path -- word-at-a-time: while the next 8 bytes all have the high
//     bit clear, skip them. Real-world text is overwhelmingly ASCII, and this runs
//     at memory speed (~35 GB/s measured).
//   * multibyte -- a direct lead-byte dispatch (2/3/4-byte), range-checking the
//     continuation bytes inline. This replaced a Hoehrmann branchless DFA: the DFA
//     costs two DEPENDENT table loads per byte (a serial latency chain that capped
//     multibyte input at ~0.74 GB/s), whereas these checks are independent and the
//     branches predict perfectly on valid text. `(x & 0xC0) == 0x80` is the "is a
//     continuation byte" test; the E0/ED and F0/F4 special cases bar overlong
//     encodings, UTF-16 surrogates, and code points past U+10FFFF.
#define UTF8_CONT(x) (((x) & 0xC0) == 0x80)
static bool utf8_is_valid(const uint8_t *b, size_t len) {
    size_t i = 0;
    while (i < len) {
        if (b[i] < 0x80) { // ASCII (single or a run)
            while (i + 8 <= len) {
                uint64_t w;
                memcpy(&w, b + i, 8);
                if (w & 0x8080808080808080ULL) break;
                i += 8;
            }
            while (i < len && b[i] < 0x80) i++;
            continue;
        }
        uint8_t c = b[i];
        if (c < 0xC2) {
            return false; // 0x80-0xBF stray continuation, or 0xC0/0xC1 overlong lead
        } else if (c < 0xE0) { // 2-byte: C2..DF 80..BF
            if (i + 2 > len || !UTF8_CONT(b[i + 1])) return false;
            i += 2;
        } else if (c < 0xF0) { // 3-byte: E0..EF
            if (i + 3 > len || !UTF8_CONT(b[i + 2])) return false;
            uint8_t b1 = b[i + 1];
            if (c == 0xE0 ? b1 < 0xA0            // overlong
                : c == 0xED ? b1 > 0x9F          // surrogate D800..DFFF
                : !UTF8_CONT(b1))
                return false;
            i += 3;
        } else if (c <= 0xF4) { // 4-byte: F0..F4
            if (i + 4 > len || !UTF8_CONT(b[i + 2]) || !UTF8_CONT(b[i + 3])) return false;
            uint8_t b1 = b[i + 1];
            if (c == 0xF0 ? b1 < 0x90            // overlong
                : c == 0xF4 ? b1 > 0x8F          // > U+10FFFF
                : !UTF8_CONT(b1))
                return false;
            i += 4;
        } else {
            return false; // 0xF5-0xFF
        }
    }
    return true;
}

// raw_text_from_bytes: validate a byte view as UTF-8 and, on success, copy it
// into an owned heap Text -- Text is not yet a zero-copy view over Bytes, so a
// valid run materialises. Returns `This text` or `Nope`, built to match codegen's
// constructor layout exactly: `Nope` is nullary (no fields), so it is the shared
// `STATIC_DATA0` instance -- a `.rodata` value, never a heap allocation.
Value utf8_from_slice(Value sv) {
    Slice *s = as_ptr(sv);
    const uint8_t *p = s->base;
    size_t n = s->len;
    if (!utf8_is_valid(p, n)) return STATIC_DATA0(0);
    // The collector is non-moving and `sv` is a live local on the C stack, so its
    // owner stays reachable and `p` stays valid across the alloc in mk_textn.
    return mk_data1(1, mk_textn((const char *)p, n));
}

// Validate only -- no allocation, no materialised Text. Used to profile/benchmark
// the validator itself (and as a fast `Text.is_valid` that never copies).
bool utf8_slice_is_valid(Value sv) {
    Slice *s = as_ptr(sv);
    return utf8_is_valid(s->base, s->len);
}

// ----------------------------------------------------------------- memory maps
// Result ordinals follow `Result ::= Fault e | Return a` -> Fault = 0, Return = 1.
// (Verify against codegen's constructor numbering before wiring the stdlib.)
Value result_return(Value x) { return mk_data(1, 1, x); }
Value result_fault(Value e) { return mk_data(0, 1, e); }

Value perhaps_this(Value x) { return mk_data(1, 1, x); }
// `Nope` is nullary: codegen emits it as a `STATIC_DATA0(0)` -- a shared, immutable
// `.rodata` instance (tag, no fields), never a heap allocation. We do the same here
// rather than reference the stdlib `Root_Stdlib_Data_Perhaps_Nope` global, which would
// chain the runtime to a symbol absent from any program that never imports Data.Perhaps.
// Matching is by tag, not identity, so this static is indistinguishable from that
// global -- and, being static, it costs no allocation on the hot Option-returning path.
Value perhaps_nope() { return STATIC_DATA0(0); }

// Ranged Buffer -> Bytes producers. Like buffer_move/buffer_copy but for a
// sub-range [off, off+n); Fault(-1) if that range runs past the buffer's length.
Value buffer_move_range(Value bv, size_t off, size_t n) {
    Buffer *b = as_ptr(bv);
    if (off + n > b->len) return result_fault(VInt(-1));
    void *body = b->bytes; // handed off below; stays live on the stack meanwhile
    void *fresh = gc_new(16, OBJ_BYTES);
    b = as_ptr(bv);
    b->bytes = fresh;
    b->len = 0;
    b->cap = 16;
    gc_remember_object(b); // old handle -> young body: record for the minor barrier
    return result_return(mk_slice(body, off, n));
}

Value buffer_copy_range(Value bv, size_t off, size_t n) {
    Buffer *b = as_ptr(bv);
    if (off + n > b->len) return result_fault(VInt(-1));
    void *body = gc_new(n ? n : 1, OBJ_BYTES);
    b = as_ptr(bv); // re-fetch after the possible collection
    memcpy(body, (const uint8_t *)b->bytes + off, n);
    return result_return(mk_slice(body, 0, n));
}

static Value mk_mmap(uint8_t *region, size_t len) {
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
// itself (no copy -- the slice's `base` points straight into `region`). Valid only
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
    size_t w = fwrite(s->base, 1, s->len, f);
    int err = (w == s->len) ? 0 : -1;
    fclose(f);
    return err;
}
