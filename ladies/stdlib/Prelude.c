// Companion implementation of the primordial Prelude's `foreign` primitives.
//
// The real work lives in the runtime (gc.c): these are thin marshalling wrappers over
// the primitive C entry points. Each FOREIGN_DECL name is the Marmelade name mangled to
// `Root_Prelude_<Submodule>_<member>` -- the symbol the compiler emits at the call site.
// The Buffer/Bytes handles are GC objects, crossing the boundary through the `Value`
// escape-hatch tag so the collector keeps tracing them.
#include <limits.h>
#include <float.h>
#include "gc.h"

// ------------------------------------------------------------------- Int
// `Int.of_char` and `Float.of_int` are now compiler builtins (see runtime.h
// prim_int_of_char / prim_float_of_int), not foreigns -- no companion needed.
FOREIGN_DECL(int64_t, Root_Prelude_Int_raw_max_of_int, { return INT_MAX; })
FOREIGN_DECL(int64_t, Root_Prelude_Int_raw_min_of_int, { return INT_MIN; })

FOREIGN_DECL(Value, Root_Prelude_Float_raw_max_of_float, { return VFloat(DBL_MAX); })
FOREIGN_DECL(Value, Root_Prelude_Float_raw_min_of_float, { return VFloat(DBL_MIN); })

// ------------------------------------------------------------ Buffer (mutable)
FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_new_buffer, int64_t, cap, {
    return mk_buffer((size_t)cap);
})
// A write is a side effect; the handle is stable, so nothing to return.
FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_put_u8, Value, buf, int64_t, byte, {
    buffer_put_u8(buf, (uint8_t)byte);
    return VUnit();
})
#define TYPED_WRITE(SUFFIX)                                                             \
    FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_put_##SUFFIX, Value, b, int64_t, v, {   \
        buffer_put_##SUFFIX(b, v);                                                      \
        return VUnit();                                                                \
    })
TYPED_WRITE(16_le) TYPED_WRITE(32_le) TYPED_WRITE(64_le)
TYPED_WRITE(16_be) TYPED_WRITE(32_be) TYPED_WRITE(64_be)
#undef TYPED_WRITE
FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_put_slice, Value, b, Value, s, {
    buffer_put_slice(b, s);
    return VUnit();
})
// raw_move : zero-copy handoff (resets the buffer); raw_copy : independent copy.
FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_move, Value, buf, { return buffer_move(buf); })
FOREIGN_DECL(Value, Root_Prelude_Buffer_raw_copy, Value, buf, { return buffer_copy(buf); })

// -------------------------------------------------------------- Bytes (view)
FOREIGN_DECL(int64_t, Root_Prelude_Bytes_raw_slice_len, Value, s, {
    return (int64_t)slice_len(s);
})
FOREIGN_DECL(Value, Root_Prelude_Bytes_raw_sub, Value, s, int64_t, off, int64_t, len, {
    return slice_sub(s, (size_t)off, (size_t)len);
})
FOREIGN_DECL(int64_t, Root_Prelude_Bytes_raw_get_u8, Value, s, int64_t, i, {
    return (int64_t)slice_get_u8(s, (size_t)i);
})
#define TYPED_READ(SUFFIX)                                                             \
    FOREIGN_DECL(int64_t, Root_Prelude_Bytes_raw_get_##SUFFIX, Value, s, int64_t, off, {\
        return (int64_t)slice_get_##SUFFIX(s, (size_t)off);                            \
    })
TYPED_READ(u16_le) TYPED_READ(u32_le) TYPED_READ(u64_le)
TYPED_READ(i16_le) TYPED_READ(i32_le) TYPED_READ(i64_le)
TYPED_READ(u16_be) TYPED_READ(u32_be) TYPED_READ(u64_be)
TYPED_READ(i16_be) TYPED_READ(i32_be) TYPED_READ(i64_be)
#undef TYPED_READ
// raw_is_valid : Bytes -> Bool  (validate-only UTF-8 fast path; no allocation)
FOREIGN_DECL(Bool, Root_Prelude_Bytes_raw_is_valid, Value, s, {
    return utf8_slice_is_valid(s);
})
