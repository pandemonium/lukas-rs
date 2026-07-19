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

#endif // MARMELADE_GC_H
