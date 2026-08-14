#include "gc.h"

/// Foreign implementation for Stdlib.Data.Hash.
///
/// `now_millis` exposes the runtime clock (declared in runtime.h) as a coarse
/// per-map seed source for `Table.make_default`. It takes a `Unit` (ignored) and
/// returns the current time in milliseconds. This is an effectful read, so the
/// `.lady` side wraps it in `IO.suspend`; the value must be recomputed per call,
/// hence an arity-1 `FOREIGN_DECL` (not the arity-0 compute-once-at-startup form).
FOREIGN_DECL(int64_t, Root_Stdlib_Data_Hash_Table_now_millis, Value, unit, {
  (void)unit;
  return now_millis();
})
