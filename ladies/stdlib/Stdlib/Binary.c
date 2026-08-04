// Companion implementation of Stdlib.Binary's `foreign` primitives -- the mmap / ranged /
// write-file entry points. The byte/buffer primitives moved to the primordial Prelude.c.
// These wrappers speak the opaque erased types (Bytes/Buffer cross as their OBJ_SLICE/
// OBJ_BUFFER Value), so no Raw_* appears here.
#include "gc.h"

// raw_move_range / raw_copy_range : Buffer -> Int -> Int -> Result Int Bytes
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_move_range, Value, buf, int64_t, off, int64_t, n, {
    return buffer_move_range(buf, (size_t)off, (size_t)n);
})
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_copy_range, Value, buf, int64_t, off, int64_t, n, {
    return buffer_copy_range(buf, (size_t)off, (size_t)n);
})

// ----------------------------------------------------------- Mmap (mapped file)
// raw_mmap_open : Text -> Result Int Raw_Mmap  (Text is an OBJ_SLICE, no NUL -> copy the path)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_open, Value, s, {
    char path[4096];
    if (!text_to_cstr(s, path, sizeof path)) return result_fault(VInt(-1));
    return mmap_open(path);
})
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_close, Value, m, {
    mmap_close(m);
    return VUnit();
})
// raw_mmap_read : Raw_Mmap -> Int -> Int -> Result Int Bytes  (copies out)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_read, Value, m, int64_t, off, int64_t, n, {
    return mmap_read(m, (size_t)off, (size_t)n);
})
// raw_mmap_slice : Raw_Mmap -> Int -> Int -> Result Int Bytes  (zero-copy view)
FOREIGN_DECL(Value, Root_Stdlib_Binary_raw_mmap_slice, Value, m, int64_t, off, int64_t, n, {
    return mmap_slice(m, (size_t)off, (size_t)n);
})
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_mmap_len, Value, m, { return mmap_len(m); })
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_mmap_get_u8, Value, m, int64_t, i, {
    return mmap_get_u8(m, i);
})
FOREIGN_DECL(Bool, Root_Stdlib_Binary_raw_mmap_closed, Value, m, { return mmap_is_closed(m); })
// raw_write_file : Bytes -> Text -> Int  (0 on success, else errno)
FOREIGN_DECL(int64_t, Root_Stdlib_Binary_raw_write_file, Value, s, Value, p, {
    char path[4096];
    if (!text_to_cstr(p, path, sizeof path)) return -1;
    return slice_write_file(s, path);
})
