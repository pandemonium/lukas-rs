// Garbage collector for the Marmelade C backend: generational, conservative
// mark-sweep, non-moving. The heap constructors live here too, since they are
// what the collector manages. See gc.c for the design.
#ifndef MARMELADE_GC_H
#define MARMELADE_GC_H

#include "runtime.h"

// Heap constructors (GC-managed). A lifted function is `Value code(Value self,
// Value arg)`; a closure stores its `nfree` captured values inline (passed
// variadically, like `mk_tuple`).
Value mk_closure(Value (*code)(Value, Value), size_t nfree, ...);
// A closure that additionally carries an uncurried worker for its curried chain
// (see `Closure` in runtime.h). `mk_closure(code, nfree, ...)` is
// `mk_closure_n(code, NULL, 1, nfree, ...)`: a single-stage closure, no fast path.
Value mk_closure_n(Value (*code)(Value, Value), Value (*worker)(Value, Value *),
                   size_t arity, size_t nfree, ...);
Value mk_tuple(size_t len, ...);

// A constructor value (see `Data` in runtime.h): an integer tag plus `nfields`
// inline field values (passed variadically). `data_len` recovers a live data
// value's field count from its heap header -- used by the collector and `show`,
// which are the only places the count isn't already known statically.
Value mk_data(uint64_t tag, size_t nfields, ...);
size_t data_len(Value v);

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

#endif // MARMELADE_GC_H
