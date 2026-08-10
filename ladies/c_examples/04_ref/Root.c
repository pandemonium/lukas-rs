// C implementation of the `Ref` module's foreign primitives. A reference cell is a
// one-element tuple (OBJ_TUPLE): the GC already traces tuple slots, so the value the
// cell holds stays live and there is no bespoke object kind to teach the collector.
#include "gc.h"

// raw_new : a -> Array a   -- allocate a one-slot cell initialised to x.
FOREIGN_DECL(Value, Root_Ref_raw_new, Value, x, {
    return mk_tuple1(x);
})

// raw_read : Array a -> a  -- read slot 0.
FOREIGN_DECL(Value, Root_Ref_raw_read, Value, cell, {
    return as_tuple(cell)->elems[0];
})

// raw_write : Array a -> a -> Unit  -- overwrite slot 0 in place. THIS is the side
// effect: the same cell now reads back a different value.
//
// GC note: under the default Immix collector (whole-heap, non-generational) a plain
// store needs no write barrier -- the next mark traces the cell's slot and reaches
// the new value. Under MARM_GC=slab (generational) an *old* cell repointed to a
// *young* value would need a remembered-set entry, exactly as mutable Buffer does
// (gc_remember_buffer in gc.c). This demo runs on the default, so the bare store is
// correct; a production Ref would gate the barrier on that path.
FOREIGN_DECL(Value, Root_Ref_raw_write, Value, cell, Value, x, {
    as_tuple(cell)->elems[0] = x;
    return VUnit();
})
