// Companion for Stdlib.Text's `raw_parse_int` (the int-parsing experiment). The UTF-8
// validator (`raw_is_valid`) and the byte primitives live in the primordial Prelude.c.
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

#include "gc.h"

static bool parse_int(const char *s, int64_t *out);
static bool parse_float(const char *s, double *out);

// raw_parse_int : Text -> Perhaps Int
// Text is an OBJ_SLICE (length-prefixed, no NUL); copy it into a small NUL-terminated
// buffer for strtol. Anything that can't be a decimal int in 63 chars can't parse anyway.
FOREIGN_DECL(Value, Root_Stdlib_Text_raw_parse_float, Value, s, {
    char text[64];
    double number;

    if (text_to_cstr(s, text, sizeof text) && parse_float(text, &number)) {
        return perhaps_this(mk_float(number));
    } else {
        return perhaps_nope();
    }
})

FOREIGN_DECL(Value, Root_Stdlib_Text_raw_parse_int, Value, s, {
    char text[64];
    int64_t number;

    if (text_to_cstr(s, text, sizeof text) && parse_int(text, &number)) {
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

static bool parse_float(const char *s, double *out)
{
    if (s == NULL || out == NULL || *s == '\0')
        return false;

    errno = 0;

    char *end;
    double value = strtod(s, &end);

    if (end == s)
        return false;

    if (errno == ERANGE)
        return false;

    /* Reject unexpected trailing characters. */
    if (*end != '\0')
        return false;

    *out = value;

    return true;
}
