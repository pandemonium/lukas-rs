// C implementation of the private `foreign` primitives in Root.lady's Bytes
// module. The Buffer/Slice handles are GC objects (see c/gc.c) and cross the
// boundary as boxed Values (the `Value` tag), so the collector keeps tracing
// them -- unlike a manually-managed FILE*, which is smuggled as an Int.
#include "gc.h"

// raw_new_buffer : Int -> Raw_Buffer
FOREIGN_DECL(Value, Root_Bytes_raw_new_buffer, int64_t, cap, {
    return mk_buffer((size_t)cap);
})
// raw_put_u8 : Raw_Buffer -> Int -> Raw_Buffer  (write is a side effect; handle is stable,
// so we just hand the same handle back for this low-level threading demo)
FOREIGN_DECL(Value, Root_Bytes_raw_put_u8, Value, buf, int64_t, byte, {
    buffer_put_u8(buf, (uint8_t)byte);
    return buf;
})
// raw_move : Raw_Buffer -> Raw_Slice
FOREIGN_DECL(Value, Root_Bytes_raw_move, Value, buf, { return buffer_move(buf); })
// raw_slice_len : Raw_Slice -> Int
FOREIGN_DECL(int64_t, Root_Bytes_raw_slice_len, Value, s, { return (int64_t)slice_len(s); })
// raw_get_u8 : Raw_Slice -> Int -> Int
FOREIGN_DECL(int64_t, Root_Bytes_raw_get_u8, Value, s, int64_t, i, {
    return (int64_t)slice_get_u8(s, (size_t)i);
})
// raw_get_i32_le : Raw_Slice -> Int -> Int
FOREIGN_DECL(int64_t, Root_Bytes_raw_get_i32_le, Value, s, int64_t, off, {
    return (int64_t)slice_get_i32_le(s, (size_t)off);
})
