// Companion implementation of Stdlib.Memory's `foreign` primitives.
//
// The real work lives in the runtime (gc.c): these are thin marshalling wrappers
// that box/unbox the primitive C entry points behind the boxed `Value`. Each
// FOREIGN_DECL name is the Marmelade name mangled to `<Module>_<member>` -- the
// same symbol the compiler emits at the call site.
//
// The Buffer/Slice/Mmap handles are GC objects (TAG_OBJECT), so -- unlike a
// manually-managed FILE* -- they cross the boundary through the `Value`
// escape-hatch tag rather than being smuggled as an Int, so the collector keeps
// tracing them.
#include "gc.h"

// ------------------------------------------------------------ Buffer (mutable)
// raw_new_buffer : Int -> Raw_Buffer
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_new_buffer, int64_t, cap, {
    return mk_buffer((size_t)cap);
})
// raw_put_u8 : Raw_Buffer -> Int -> Unit  (a write is a side effect; the handle is stable)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_put_u8, Value, buf, int64_t, byte, {
    buffer_put_u8(buf, (uint8_t)byte);
    return VUnit();
})
// raw_move : Raw_Buffer -> Raw_Slice  (zero-copy: the slice takes the buffer's bytes)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_move, Value, buf, { return buffer_move(buf); })
// raw_copy : Raw_Buffer -> Raw_Slice  (independent, exact-size copy)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_copy, Value, buf, { return buffer_copy(buf); })
// raw_move_range / raw_copy_range : Raw_Buffer -> Int -> Int -> Result Int Raw_Slice
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_move_range, Value, buf, int64_t, off, int64_t, n, {
    return buffer_move_range(buf, (size_t)off, (size_t)n);
})
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_copy_range, Value, buf, int64_t, off, int64_t, n, {
    return buffer_copy_range(buf, (size_t)off, (size_t)n);
})

// Typed writes (one per width x endianness; signed/unsigned share bytes).
#define TYPED_WRITE(SUFFIX)                                                             \
    FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_put_##SUFFIX, Value, b, int64_t, v, {    \
        buffer_put_##SUFFIX(b, v);                                                      \
        return VUnit();                                                                \
    })
TYPED_WRITE(16_le) TYPED_WRITE(32_le) TYPED_WRITE(64_le)
TYPED_WRITE(16_be) TYPED_WRITE(32_be) TYPED_WRITE(64_be)
#undef TYPED_WRITE

// raw_put_slice : Raw_Buffer -> Raw_Slice -> Unit  (append a slice's bytes)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_put_slice, Value, b, Value, s, {
    buffer_put_slice(b, s);
    return VUnit();
})

// -------------------------------------------------------------- Slice (view)
// raw_slice_len : Raw_Slice -> Int
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_slice_len, Value, s, {
    return (int64_t)slice_len(s);
})
// raw_get_u8 : Raw_Slice -> Int -> Int
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_get_u8, Value, s, int64_t, i, {
    return (int64_t)slice_get_u8(s, (size_t)i);
})
// raw_sub : Raw_Slice -> Int -> Int -> Raw_Slice
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_sub, Value, s, int64_t, off, int64_t, len, {
    return slice_sub(s, (size_t)off, (size_t)len);
})

// Typed reads. Twelve near-identical wrappers over the runtime primitives; the
// macro keeps them honest. (A read wider than i64's range wraps -- Marmelade's
// only integer type is a signed 64-bit Int.)
#define TYPED_READ(SUFFIX)                                                             \
    FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_get_##SUFFIX, Value, s, int64_t, off, {    \
        return (int64_t)slice_get_##SUFFIX(s, (size_t)off);                            \
    })
TYPED_READ(u16_le) TYPED_READ(u32_le) TYPED_READ(u64_le)
TYPED_READ(i16_le) TYPED_READ(i32_le) TYPED_READ(i64_le)
TYPED_READ(u16_be) TYPED_READ(u32_be) TYPED_READ(u64_be)
TYPED_READ(i16_be) TYPED_READ(i32_be) TYPED_READ(i64_be)
#undef TYPED_READ

// ----------------------------------------------------------- Mmap (mapped file)
// raw_mmap_open : Text -> Result Int Raw_Mmap
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_open, Text, path, { return mmap_open(path); })
// raw_mmap_close : Raw_Mmap -> Unit
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_close, Value, m, {
    mmap_close(m);
    return VUnit();
})
// raw_mmap_read : Raw_Mmap -> Int -> Int -> Result Int Raw_Slice  (copies out)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_read, Value, m, int64_t, off, int64_t, n, {
    return mmap_read(m, (size_t)off, (size_t)n);
})
// raw_mmap_slice : Raw_Mmap -> Int -> Int -> Result Int Raw_Slice  (zero-copy view)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_slice, Value, m, int64_t, off, int64_t, n, {
    return mmap_slice(m, (size_t)off, (size_t)n);
})
// Direct mmap reads for Byte_Source Mmap.
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_mmap_len, Value, m, { return mmap_len(m); })
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_mmap_get_u8, Value, m, int64_t, i, {
    return mmap_get_u8(m, i);
})
FOREIGN_DECL(Bool, Root_Stdlib_Binary_raw_mmap_closed, Value, m, { return mmap_is_closed(m); })
// raw_write_file : Raw_Slice -> Text -> Int  (0 on success, else errno)
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_write_file, Value, s, Text, path, {
    return slice_write_file(s, path);
})
