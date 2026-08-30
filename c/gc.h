// Garbage collector for the Marmelade C backend: generational, conservative
// mark-sweep, non-moving. The heap constructors live here too, since they are
// what the collector manages. See gc.c for the design.
#ifndef MARMELADE_GC_H
#define MARMELADE_GC_H

#include "runtime.h"
#include <string.h> // memcmp, for the inline Text comparison below

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
  OBJ_MMAP,  // handle to a memory-mapped region (region lives outside the heap)
  OBJ_SLICE, // immutable view; owner is an OBJ_BYTES body or an OBJ_MMAP handle
  OBJ_FLOAT, // boxed IEEE-754 double (leaf); a 64-bit float cannot be an
             // immediate
  OBJ_KIND_COUNT, // number of object kinds; sizes the per-kind stat tables
} ObjKind;

// Prepended to every heap object; a Value pointer names the body just past the
// header, so HEADER/BODY convert between the two.
typedef struct GcHeader {
  // 8-byte header (was 24). Small objects -- the overwhelming majority -- carry
  // no generation-list link: slab objects are bitmap-swept and Immix objects
  // are line-reclaimed, so only large (malloc'd) objects need enumeration, and
  // they live in a side array (`gc_large`) rather than an intrusive `next`.
  // `body` is a uint32 because no single object approaches 4 GiB (small objects
  // are <= 512 B; large ones are realistic buffers/strings). Shrinking the
  // header from 24 to 8 bytes cuts allocation *volume* -- the dominant cost on
  // these alloc-bound workloads -- by 16 B/object (e.g. a `mk_data1` 40 B -> 24
  // B).
  uint32_t body; // body size in bytes (excludes this header)
  uint8_t mark;
  uint8_t kind; // ObjKind
  uint8_t old;  // 0 = young (nursery), 1 = tenured, MARM_ETERNAL = static
  // Constructor tag for an OBJ_DATA value: which constructor of its sum type.
  // Lives in the header's former padding byte (header stays 8 B) instead of a
  // full body word, shrinking every constructor node by 8 B -- the dominant
  // object on recursive-structure workloads. Unused (garbage, never read) for
  // other kinds, since `data_tag` is only emitted for constructor values.
  uint8_t ctag;
} GcHeader;

#define BODY(h) ((void *)((h) + 1))
#define HEADER(p) (((GcHeader *)(p)) - 1)

// An immutable byte view. `base` is the RESOLVED read pointer, computed once when
// the slice is built; reading a byte is then a single load, with no dispatch on how
// the bytes are owned. Valid because the collector is non-moving. `owner` exists
// purely so the tracer keeps the backing alive -- an OBJ_BYTES body, an OBJ_MMAP
// handle, the parent OBJ_SLICE of a sub-view of an inline-owned slice, or NULL when
// the bytes sit immediately behind this slice's own header (see `mk_textn`). It is
// never followed to find the bytes. Both `Bytes` and the validated `Text` erase to
// an OBJ_SLICE over this. Exposed here (not gc.c-private) so codegen can emit a
// string literal as a static .rodata Slice.
typedef struct {
  void *owner;
  const uint8_t *base;
  size_t len;
} Slice;

// A `GcHeader.old` sentinel marking a static, never-collected object: a
// borrowed string literal's descriptor, emitted `const` into .rodata by
// codegen. It is not in any slab or the large-object set (so `is_object` is
// false for it and the conservative scan and sweep never see it); the one place
// the precise tracer can reach it -- as a child Value of a heap object -- is
// guarded in `mark_obj`, which early-returns on this sentinel (crucial: the
// descriptor is `const`, so its `mark` bit must never be written).
#define MARM_ETERNAL 2

// A capture-free (arity-0) closure is identical and immutable for a given
// code/worker/arity, so codegen emits ONE static instance instead of allocating
// one per use (arity-0 closures were ~8-14% of all allocation on the monad
// benchmarks). Like a borrowed-string descriptor it is `MARM_ETERNAL`, so the
// collector never marks or frees it (its `const` storage is thus never
// written). The body is a single `desc` pointer (no captures), so the tracer
// visits no fields. `VObject(&__sc.desc)` is the body pointer (past the 8-byte
// header).
#define STATIC_CLOSURE0(code_fn, worker_fn, arity_n)                           \
  ({                                                                           \
    static const ClosureDesc __d = {(code_fn), (worker_fn), (arity_n)};        \
    static const struct {                                                      \
      GcHeader gch;                                                            \
      const ClosureDesc *desc;                                                 \
    } __sc = {{sizeof(Closure), 0, OBJ_CLOSURE, MARM_ETERNAL}, &__d};          \
    VObject((void *)&__sc.desc);                                               \
  })

// A nullary constructor (a sum-type tag with no fields) is identical and
// immutable for a given tag, so -- exactly like STATIC_CLOSURE0 -- codegen
// emits ONE static instance per use site instead of allocating a fresh Data on
// every mention (nullary constructors like
// `Nil`/`None`/`Less`/`Equal`/`Greater` were otherwise a heap alloc each).
// MARM_ETERNAL keeps the collector off its `const` storage: `is_object` is
// false for it (on no slab or large-object list, so the conservative scan and
// sweep never see it) and `mark_obj` early-returns on the sentinel. The tag now
// lives in the header's `ctag` byte (not a body word), so the body is empty (0
// fields) -- `data_len` recovers 0 and the tracer visits nothing. The body
// pointer is just past the 8-byte header, which is what `data_tag` reads back
// (via `HEADER(...)->ctag`).
// `_Alignas(16)`: this struct is only a GcHeader (4-byte alignment), but every
// object body must be 8-aligned like the heap allocator's -- the tagged-value
// representation reserves the low bits of a pointer, so a body must never carry
// spare low bits. Heap bodies get this from `gc_new`; this static forces it.
#define STATIC_DATA0(tagv)                                                     \
  ({                                                                           \
    _Alignas(16) static const struct {                                         \
      GcHeader gch;                                                            \
    } __sd = {{0, 0, OBJ_DATA, MARM_ETERNAL, (tagv)}};                         \
    VObject((void *)((const char *)&__sd + sizeof(GcHeader)));                 \
  })

// A float *literal* is a fixed, immutable double, so -- like STATIC_DATA0 --
// codegen emits ONE immortal `.rodata` box per literal instead of
// heap-allocating on every mention. OBJ_FLOAT is a leaf (no child Values), and
// MARM_ETERNAL keeps the collector off its `const` storage. The body is exactly
// `sizeof(double)`, matching `mk_float`, so `as_float` reads the same layout
// whether the box is static or heap-allocated. `VObject(&__sf.f)` is the body
// pointer (past the 8-byte header).
#define STATIC_FLOAT(x)                                                        \
  ({                                                                           \
    static const struct {                                                      \
      GcHeader gch;                                                            \
      double f;                                                                \
    } __sf = {{sizeof(double), 0, OBJ_FLOAT, MARM_ETERNAL}, (x)};              \
    VObject((void *)&__sf.f);                                                  \
  })

Value result_return(Value x);
Value result_fault(Value e);

Value perhaps_this(Value x);
Value perhaps_nope();

// Heap constructors (GC-managed). A lifted function is `Value code(Value self,
// Value arg)`; a closure stores a pointer to its shared static `ClosureDesc`
// (`code`/`worker`/`arity`, see runtime.h) plus its `nfree` captured values
// inline (passed variadically, like `mk_tuple`).
Value mk_closure_dn(const ClosureDesc *desc, size_t nfree, ...);
// Compatibility builders (code/worker/arity instead of a static descriptor) for
// the runtime builtins and `FOREIGN_DECL` companions; they intern a shared
// descriptor.
Value mk_closure(Value (*code)(Value, Value), size_t nfree, ...);
Value mk_closure_n(Value (*code)(Value, Value), Value (*worker)(Value, Value *),
                   size_t arity, size_t nfree, ...);
Value mk_tuple(size_t len, ...);
Value mk_tuple_uninit(size_t len);

// Flat mutable arrays: one heap object holding all `count` elements' leaves
// inline, so an array of nested products is a single GC object (see the
// flat-array section in gc.c). `flat_generate` builds one by calling
// `mk_element` per index, discovering the element's product shape from element
// 0; get/put rebuild / pack the flat<->canonical coercion. Backing the
// `Mutable_Array` foreigns.
Value flat_generate(int64_t length, Value mk_element);
Value mk_flat_array_from(size_t n, Value *elems);
// Like `mk_flat_array_from` but with a caller-supplied, type-driven element shape
// (may contain inlined-sum nodes, which element-0 discovery cannot). See gc.c.
Value mk_flat_array_from_shaped(size_t n, Value *elems, const int64_t *shape, size_t slen);
// Like `flat_generate` but with a caller-supplied, type-driven shape (from the
// `Memory_Layout` dictionary) so sum elements pack inline. See gc.c.
Value flat_generate_shaped(int64_t length, Value mk_element, const int64_t *shape, size_t slen);
// Allocate an exactly-sized shaped array and initialize it by consuming an
// enumeration. Each successful step is written at `index`, after which index is
// advanced by `stride`. The Enumeratee witness promises at least `length` steps.
Value flat_from_enumerator_shaped(int64_t length, Value enumeration, Value next,
                                  const int64_t *shape, size_t slen);
// Element-0-discovering counterpart used when Memory_Layout carries no explicit
// sum shape, preserving the product flattening behaviour of `flat_generate`.
Value flat_from_enumerator(int64_t length, Value enumeration, Value next);
size_t flat_array_count(Value arr);
Value flat_array_get(Value arr, size_t i);
// Read field 0 of the payload constructor from a top-level unary niche sum,
// without rebuilding the enclosing coproduct. The caller guarantees that slot
// `i` contains the payload constructor and that `i` is in bounds.
Value flat_array_get_niche_payload_unchecked(Value arr, size_t i);
void flat_array_set(Value arr, size_t i, Value elt);
Value flat_array_put(Value arr, size_t i, Value elt);
// Copy a range of packed elements without boxing them out. Source and target
// must have the same element layout; ranges may overlap (memmove semantics).
void flat_array_copy(Value source, size_t source_index, Value target,
                     size_t target_index, size_t count);
// Allocate a larger array with the source's exact packed layout, copy every
// existing element, and initialize the new suffix from one constant value.
Value flat_array_grow_with(Value source, size_t new_count, Value fill);
// Read one statically-known leaf directly from packed element storage, without
// rebuilding the canonical aggregate around it.
Value flat_array_get_word(Value arr, size_t i, size_t word_offset);
void flat_array_set_word(Value arr, size_t i, size_t word_offset, Value value);

// Box a double on the heap (OBJ_FLOAT leaf). A 64-bit IEEE-754 value cannot
// share the word with the immediate tag bit, so every computed Float is a heap
// box; `as_float` reads it back. Float *literals* skip this via the immortal
// STATIC_FLOAT box above.
Value mk_float(double x);

// A constructor value (see `Data` in runtime.h): an integer tag plus `nfields`
// inline field values (passed variadically). `data_len` recovers a live data
// value's field count from its heap header -- used by the collector and `show`,
// which are the only places the count isn't already known statically.
Value mk_data(uint64_t tag, size_t nfields, ...);
// Copy-out for inlined sums: rebuild a boxed OBJ_DATA from an inline tag +
// payload region (see gc.c). Backing the flat-layout inlined-sum reads.
Value mk_data_inline(Value tag_imm, size_t payload_words, const Value *src);
size_t data_len(Value v);

// A constructor value's tag (which constructor), read from the header's `ctag`
// byte. Lives here (not runtime.h) because it needs `GcHeader`/`HEADER`. Only
// emitted for values codegen knows are constructors.
#define data_tag(v) (HEADER(as_data(v))->ctag)
// Element count of a tuple / Array, recovered the same way (tuples store no
// length).
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
Value mk_closure_d4(const ClosureDesc *desc, Value c0, Value c1, Value c2,
                    Value c3);

// Owned (collectable) strings. Borrowed literals stay as `VText("...")` -- a
// bare pointer into read-only data, never a GC object. `mk_text*` copy into the
// heap, where the collector reclaims them once unreachable.
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
Value mk_buffer(size_t cap);
void buffer_put_u8(Value buf,
                   uint8_t byte); // in-place write; the handle is stable
void buffer_put_bytes(Value buf, const uint8_t *src, size_t n);
void buffer_put_16_le(Value buf, int64_t v);
void buffer_put_32_le(Value buf, int64_t v);
void buffer_put_64_le(Value buf, int64_t v);
void buffer_put_16_be(Value buf, int64_t v);
void buffer_put_32_be(Value buf, int64_t v);
void buffer_put_64_be(Value buf, int64_t v);
void buffer_put_slice(Value buf, Value slice);
size_t buffer_len(Value buf);
Value buffer_move(Value buf); // -> Slice sharing the buffer's body (caller must
                              // not reuse buf)
Value buffer_copy(
    Value buf); // -> Slice over a fresh copy of the buffer's bytes
Value buffer_move_range(Value buf, size_t off,
                        size_t n); // -> Result(Fault -1 | Return Slice);
                                   // zero-copy [off,off+n), resets buf
Value buffer_copy_range(Value buf, size_t off,
                        size_t n); // -> Result; independent copy of [off,off+n)

Value mk_slice(void *owner, size_t offset, size_t len);
// Build a slice over an ALREADY-resolved read pointer. `owner` is only the
// liveness link (see the `Slice` comment); `base` must point into whatever it
// keeps alive.
Value mk_slice_at(void *owner, const uint8_t *base, size_t len);

// The hot accessors. Each is a single load because the base pointer was resolved
// once, at construction -- no owner dereference, no kind dispatch, no recursion.
// They live in the header (not gc.c) so they inline into the generated program and
// the stdlib companions, which are separate translation units: `Bytes.get_u8` in a
// scanning loop then folds to `base[i]` at the call site instead of three calls.
static inline const uint8_t *slice_ptr(Value slice) {
  return ((const Slice *)as_ptr(slice))->base;
}
static inline size_t slice_len(Value slice) {
  return ((const Slice *)as_ptr(slice))->len;
}
static inline uint8_t slice_get_u8(Value slice, size_t i) {
  return ((const Slice *)as_ptr(slice))->base[i];
}

// Monomorphic `=` on Text. `val_eq` is the polymorphic fallback: it must first
// decide what it was handed, which costs two dependent loads into the operands'
// object headers just to confirm a kind codegen already knew statically. When both
// sides of `=` are Text, codegen emits this instead -- Text is always an OBJ_SLICE
// (OBJ_TEXT is a legacy enum value nothing constructs), so the length check and the
// byte compare can happen directly. Worth having as its own prim because a hash
// table's probe runs it once per lookup.
static inline Value prim_text_eq(Value a, Value b) {
  const Slice *x = (const Slice *)as_ptr(a);
  const Slice *y = (const Slice *)as_ptr(b);
  return VBool(x->len == y->len &&
               (x->base == y->base || memcmp(x->base, y->base, x->len) == 0));
}

bool text_to_cstr(Value slice, char *buf,
                  size_t cap); // NUL-terminate into buf; false if too big
Value slice_sub(Value slice, size_t offset, size_t len);

uint16_t slice_get_u16_le(Value slice, size_t off);
uint32_t slice_get_u32_le(Value slice, size_t off);
uint64_t slice_get_u64_le(Value slice, size_t off);
int16_t slice_get_i16_le(Value slice, size_t off);
int32_t slice_get_i32_le(Value slice, size_t off);
int64_t slice_get_i64_le(Value slice, size_t off);
uint16_t slice_get_u16_be(Value slice, size_t off);
uint32_t slice_get_u32_be(Value slice, size_t off);
uint64_t slice_get_u64_be(Value slice, size_t off);
int16_t slice_get_i16_be(Value slice, size_t off);
int32_t slice_get_i32_be(Value slice, size_t off);
int64_t slice_get_i64_be(Value slice, size_t off);

// Memory-mapped files. `mmap_open` returns a Result (Fault errno | Return
// Mmap); `mmap_close` munmaps (idempotent); `mmap_read` copies a range out into
// a Slice.
Value mmap_open(const char *path);
void mmap_close(Value mmap);
Value mmap_read(Value mmap, size_t off,
                size_t n); // copies out into a heap Slice
Value mmap_slice(Value mmap, size_t off,
                 size_t n); // zero-copy Slice borrowing the region

int64_t mmap_len(Value mmap); // direct mapped-region reads (Byte_Source Mmap)
int64_t mmap_get_u8(Value mmap, int64_t i);
bool mmap_is_closed(Value mmap);

// Write a slice's bytes to a file (truncating). Returns 0 on success, else
// errno.
int64_t slice_write_file(Value slice, const char *path);

// Validate a Bytes view (OBJ_SLICE) as UTF-8; on success copy it into an owned
// heap Text. Returns `This text` (Perhaps tag 1) or `Nope` (tag 0).
Value utf8_from_slice(Value slice);
// Validate only (no allocation): true iff the whole view is well-formed UTF-8.
bool utf8_slice_is_valid(Value slice);

#endif // MARMELADE_GC_H
