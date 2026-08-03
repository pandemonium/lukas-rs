// Companion implementation of Stdlib.Text's `foreign` primitives.
//
// The real work (UTF-8 validation + materialising an owned Text) lives in the
// runtime (gc.c :: utf8_from_slice); this is the thin marshalling wrapper. A
// `Bytes` is a newtype over its raw slice and erases to it, so the argument
// arrives as the OBJ_SLICE Value directly -- no unwrapping needed here.
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

#include "gc.h"

static bool parse_int(const char *s, int64_t *out);

// raw_text_from_bytes : Bytes -> Perhaps Text  (UTF-8 validate; This on success, else Nope)
FOREIGN_DECL(Value, Root_Stdlib_Text_raw_text_from_bytes, Value, s, {
    return utf8_from_slice(s);
})

// raw_is_valid : Bytes -> Bool  (validate only; no allocation, no materialised Text)
FOREIGN_DECL(Bool, Root_Stdlib_Text_raw_is_valid, Value, s, {
    return utf8_slice_is_valid(s);
})

// raw_parse_int : Text -> Perhaps Int
FOREIGN_DECL(Value, Root_Stdlib_Text_raw_parse_int, Value, s, {
    const char* text = as_text(s);
    int64_t number;

    if (parse_int(text, &number)) {
        return perhaps_this(VInt(number));
    } else {
        return perhaps_nope();
    }
})

static bool parse_int(const char *s, int64_t *out)
{
    if (s == NULL || out == NULL || *s == '\0')
        return false;

    errno = 0;
    char *end;
    long value = strtol(s, &end, 10);

    if (end == s)                 // no digits
        return false;

    if (*end != '\0')             // trailing characters
        return false;

    if (errno == ERANGE ||
        value < INT_MIN ||
        value > INT_MAX)
        return false;

    *out = (int)value;
    return true;
}
