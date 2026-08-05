// Garbage collector for the Marmelade C backend: generational, conservative
// mark-sweep, non-moving. The heap constructors live here too, since they are
// what the collector manages. See gc.c for the design.
#ifndef MARMELADE_GC_H
#define MARMELADE_GC_H

#include "runtime.h"

// Heap-object kind (selects a body's layout + tracing). Exposed here -- not
// gc.c-private -- so the emitted code can build static text descriptors for
// borrowed string literals (see notes/tagged-value.md, Stage 1b).
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

// Prepended to every heap object; a Value pointer names the body just past the
// header, so HEADER/BODY convert between the two.
typedef struct GcHeader {
    // 8-byte header (was 24). Small objects -- the overwhelming majority -- carry no
    // generation-list link: slab objects are bitmap-swept and Immix objects are
    // line-reclaimed, so only large (malloc'd) objects need enumeration, and they
    // live in a side array (`gc_large`) rather than an intrusive `next`. `body` is a
    // uint32 because no single object approaches 4 GiB (small objects are <= 512 B;
    // large ones are realistic buffers/strings). Shrinking the header from 24 to 8
    // bytes cuts allocation *volume* -- the dominant cost on these alloc-bound
    // workloads -- by 16 B/object (e.g. a `mk_data1` 40 B -> 24 B).
    uint32_t body;         // body size in bytes (excludes this header)
    uint8_t mark;
    uint8_t kind; // ObjKind
    uint8_t old;  // 0 = young (nursery), 1 = tenured, MARM_ETERNAL = static
} GcHeader;

#define BODY(h) ((void *)((h) + 1))
#define HEADER(p) (((GcHeader *)(p)) - 1)

// An immutable byte view: `owner` is a real GC-body pointer (an OBJ_BYTES body or an
// OBJ_MMAP handle -- so the tracer keeps the backing live) plus an offset/length.
// Both `Bytes` and the validated `Text` erase to an OBJ_SLICE over this. Exposed here
// (not gc.c-private) so codegen can emit a string literal as a static .rodata Slice.
typedef struct { void *owner; size_t offset; size_t len; } Slice;

// A `GcHeader.old` sentinel marking a static, never-collected object: a borrowed
// string literal's descriptor, emitted `const` into .rodata by codegen. It is
// not in any slab or the large-object set (so `is_object` is false for it and
// the conservative scan and sweep never see it); the one place the precise
// tracer can reach it -- as a child Value of a heap object -- is guarded in
// `mark_obj`, which early-returns on this sentinel (crucial: the descriptor is
// `const`, so its `mark` bit must never be written).
#define MARM_ETERNAL 2

// A capture-free (arity-0) closure is identical and immutable for a given
// code/worker/arity, so codegen emits ONE static instance instead of allocating one
// per use (arity-0 closures were ~8-14% of all allocation on the monad benchmarks).
// Like a borrowed-string descriptor it is `MARM_ETERNAL`, so the collector never marks
// or frees it (its `const` storage is thus never written). The body is a single `desc`
// pointer (no captures), so the tracer visits no fields. `VObject(&__sc.desc)` is the
// body pointer (past the 8-byte header).
#define STATIC_CLOSURE0(code_fn, worker_fn, arity_n)                                    \
    ({ static const ClosureDesc __d = {(code_fn), (worker_fn), (arity_n)};              \
       static const struct { GcHeader gch; const ClosureDesc *desc; } __sc =            \
           {{sizeof(Closure), 0, OBJ_CLOSURE, MARM_ETERNAL}, &__d};                     \
       VObject((void *)&__sc.desc); })

// A nullary constructor (a sum-type tag with no fields) is identical and immutable for
// a given tag, so -- exactly like STATIC_CLOSURE0 -- codegen emits ONE static instance
// per use site instead of allocating a fresh Data on every mention (nullary
// constructors like `Nil`/`None`/`Less`/`Equal`/`Greater` were otherwise a heap alloc
// each). MARM_ETERNAL keeps the collector off its `const` storage: `is_object` is false
// for it (on no slab or large-object list, so the conservative scan and sweep never see
// it) and `mark_obj` early-returns on the sentinel, so the tag word is never written.
// The body is exactly `sizeof(Data)` -- just the tag, no fields -- matching `mk_data0`,
// so `data_len` recovers 0 fields and the tracer visits nothing. `VObject(&__sd.tag)`
// is the body pointer (past the 8-byte header), which is what `data_tag` reads.
#define STATIC_DATA0(tagv)                                                              \
    ({ static const struct { GcHeader gch; uint64_t tag; } __sd =                       \
           {{sizeof(Data), 0, OBJ_DATA, MARM_ETERNAL}, (tagv)};                         \
       VObject((void *)&__sd.tag); })

Value result_return(Value x);
Value result_fault(Value e);

Value perhaps_this(Value x);
Value perhaps_nope();

// Heap constructors (GC-managed). A lifted function is `Value code(Value self,
// Value arg)`; a closure stores a pointer to its shared static `ClosureDesc`
// (`code`/`worker`/`arity`, see runtime.h) plus its `nfree` captured values inline
// (passed variadically, like `mk_tuple`).
Value mk_closure_dn(const ClosureDesc *desc, size_t nfree, ...);
// Compatibility builders (code/worker/arity instead of a static descriptor) for the
// runtime builtins and `FOREIGN_DECL` companions; they intern a shared descriptor.
Value mk_closure(Value (*code)(Value, Value), size_t nfree, ...);
Value mk_closure_n(Value (*code)(Value, Value), Value (*worker)(Value, Value *),
                   size_t arity, size_t nfree, ...);
Value mk_tuple(size_t len, ...);

// A constructor value (see `Data` in runtime.h): an integer tag plus `nfields`
// inline field values (passed variadically). `data_len` recovers a live data
// value's field count from its heap header -- used by the collector and `show`,
// which are the only places the count isn't already known statically.
Value mk_data(uint64_t tag, size_t nfields, ...);
size_t data_len(Value v);
// Element count of a tuple / Array, recovered the same way (tuples store no length).
size_t tuple_len(Value v);

// Fixed-arity constructors for the common small field counts. Codegen knows the
// count statically and emits these to skip the variadic `va_list`/copy-loop tax
// (and let the reserve+bump path inline); the variadic forms above remain the
// fallback for larger arities. See gc.c.
Value mk_data0(uint64_t tag);
Value mk_data1(uint64_t tag, Value f0);
Value mk_data2(uint64_t tag, Value f0, Value f1);
Value mk_data3(uint64_t tag, Value f0, Value f1, Value f2);
Value mk_data4(uint64_t tag, Value f0, Value f1, Value f2, Value f3);
Value mk_tuple0(void);
Value mk_tuple1(Value e0);
Value mk_tuple2(Value e0, Value e1);
Value mk_tuple3(Value e0, Value e1, Value e2);
Value mk_tuple4(Value e0, Value e1, Value e2, Value e3);
Value mk_closure_d0(const ClosureDesc *desc);
Value mk_closure_d1(const ClosureDesc *desc, Value c0);
Value mk_closure_d2(const ClosureDesc *desc, Value c0, Value c1);
Value mk_closure_d3(const ClosureDesc *desc, Value c0, Value c1, Value c2);
Value mk_closure_d4(const ClosureDesc *desc, Value c0, Value c1, Value c2, Value c3);

// Owned (collectable) strings. Borrowed literals stay as `VText("...")` -- a bare
// pointer into read-only data, never a GC object. `mk_text*` copy into the heap,
// where the collector reclaims them once unreachable.
Value mk_text(const char *src);
Value mk_textn(const char *src, size_t len);

// The emitted program must call `gc_init(&anchor)` as the first thing in `main`
// -- `anchor` is any local, and its address marks the bottom of the stack the
// collector scans -- and must define the global-root table below (every
// top-level `Value` the collector treats as a root; builtins are rooted inside
// the runtime).
void gc_init(void *stack_bottom);
void gc_collect(void);
extern Value *const gc_user_roots[];
extern const size_t gc_user_roots_count;

// --------------------------------------------------------------- byte buffers
// Three GC object kinds for byte handling (see gc.c). A Buffer is a mutable,
// growable heap byte region; a Slice is an immutable view that borrows a Buffer
// or an Mmap; an Mmap is a handle to a memory-mapped file whose region lives
// outside the GC heap (released manually, never by the collector).
Value  mk_buffer(size_t cap);
void   buffer_put_u8(Value buf, uint8_t byte);   // in-place write; the handle is stable
void   buffer_put_bytes(Value buf, const uint8_t *src, size_t n);
void   buffer_put_16_le(Value buf, int64_t v);
void   buffer_put_32_le(Value buf, int64_t v);
void   buffer_put_64_le(Value buf, int64_t v);
void   buffer_put_16_be(Value buf, int64_t v);
void   buffer_put_32_be(Value buf, int64_t v);
void   buffer_put_64_be(Value buf, int64_t v);
void   buffer_put_slice(Value buf, Value slice);
size_t buffer_len(Value buf);
Value  buffer_move(Value buf); // -> Slice sharing the buffer's body (caller must not reuse buf)
Value  buffer_copy(Value buf); // -> Slice over a fresh copy of the buffer's bytes
Value  buffer_move_range(Value buf, size_t off, size_t n); // -> Result(Fault -1 | Return Slice); zero-copy [off,off+n), resets buf
Value  buffer_copy_range(Value buf, size_t off, size_t n); // -> Result; independent copy of [off,off+n)

Value   mk_slice(void *owner, size_t offset, size_t len);
size_t  slice_len(Value slice);
const uint8_t *slice_ptr(Value slice); // direct read pointer to byte 0 (owner must stay live)
bool text_to_cstr(Value slice, char *buf, size_t cap); // NUL-terminate into buf; false if too big
uint8_t slice_get_u8(Value slice, size_t i);
Value   slice_sub(Value slice, size_t offset, size_t len);

uint16_t slice_get_u16_le(Value slice, size_t off);
uint32_t slice_get_u32_le(Value slice, size_t off);
uint64_t slice_get_u64_le(Value slice, size_t off);
int16_t  slice_get_i16_le(Value slice, size_t off);
int32_t  slice_get_i32_le(Value slice, size_t off);
int64_t  slice_get_i64_le(Value slice, size_t off);
uint16_t slice_get_u16_be(Value slice, size_t off);
uint32_t slice_get_u32_be(Value slice, size_t off);
uint64_t slice_get_u64_be(Value slice, size_t off);
int16_t  slice_get_i16_be(Value slice, size_t off);
int32_t  slice_get_i32_be(Value slice, size_t off);
int64_t  slice_get_i64_be(Value slice, size_t off);

// Memory-mapped files. `mmap_open` returns a Result (Fault errno | Return Mmap);
// `mmap_close` munmaps (idempotent); `mmap_read` copies a range out into a Slice.
Value mmap_open(const char *path);
void  mmap_close(Value mmap);
Value mmap_read(Value mmap, size_t off, size_t n);   // copies out into a heap Slice
Value mmap_slice(Value mmap, size_t off, size_t n);  // zero-copy Slice borrowing the region

int64_t mmap_len(Value mmap);                        // direct mapped-region reads (Byte_Source Mmap)
int64_t mmap_get_u8(Value mmap, int64_t i);
bool    mmap_is_closed(Value mmap);

// Write a slice's bytes to a file (truncating). Returns 0 on success, else errno.
int64_t slice_write_file(Value slice, const char *path);

// Validate a Bytes view (OBJ_SLICE) as UTF-8; on success copy it into an owned
// heap Text. Returns `This text` (Perhaps tag 1) or `Nope` (tag 0).
Value utf8_from_slice(Value slice);
// Validate only (no allocation): true iff the whole view is well-formed UTF-8.
bool utf8_slice_is_valid(Value slice);

#endif // MARMELADE_GC_H
