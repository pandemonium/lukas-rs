// Companion implementation of Stdlib.Text's `foreign` primitives.
//
// The real work (UTF-8 validation + materialising an owned Text) lives in the
// runtime (gc.c :: utf8_from_slice); this is the thin marshalling wrapper. A
// `Bytes` is a newtype over its raw slice and erases to it, so the argument
// arrives as the OBJ_SLICE Value directly -- no unwrapping needed here.
#include "gc.h"

// raw_text_from_bytes : Bytes -> Perhaps Text  (UTF-8 validate; This on success, else Nope)
FOREIGN_DECL(Value, Root_Stdlib_Text_raw_text_from_bytes, Value, s, {
    return utf8_from_slice(s);
})
// raw_is_valid : Bytes -> Bool  (validate only; no allocation, no materialised Text)
FOREIGN_DECL(Bool, Root_Stdlib_Text_raw_is_valid, Value, s, {
    return utf8_slice_is_valid(s);
})
