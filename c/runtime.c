#include "runtime.h"

#include "gc.h" // mk_closure / mk_tuple

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

int64_t now_millis(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t)tv.tv_sec * 1000 + (int64_t)tv.tv_usec / 1000;
}

// A curried binary builtin: stage 1 captures the first argument, stage 2
// applies the primitive PRIM. These closures exist only for partial/higher-order
// use; saturated calls go straight to the `prim_*` functions (see runtime.h).
#define BINOP(NAME, PRIM)                                                      \
    static Value NAME##_2(Value self, Value y) {                               \
        return PRIM(env_get(self, 0), y);                                      \
    }                                                                          \
    static Value NAME##_1(Value self, Value x) {                               \
        (void)self;                                                            \
        return mk_closure(NAME##_2, 1, x);                                     \
    }                                                                          \
    Value NAME

// A unary builtin: its closure just forwards to PRIM.
#define UNOP(NAME, PRIM)                                                        \
    static Value NAME##_1(Value self, Value x) {                               \
        (void)self;                                                            \
        return PRIM(x);                                                        \
    }                                                                          \
    Value NAME

bool val_eq(Value a, Value b) {
    // Immediates (Int/Bool/Char/Unit) compare by word identity: two immediate values
    // are equal exactly when their words match, so no per-kind tag is needed. A
    // well-typed `=` only ever compares two values of the same type, so if one side
    // is an immediate the other is too (and a stray immediate-vs-pointer mix still
    // compares unequal, since their words differ). Compound values (tuples, sum types)
    // are never compared here -- their equality is structural and lives in `Eq`
    // witnesses that recurse through the leaves -- so only Text needs the pointer path.
    if (a.w & IMM_TAG) {
        return a.w == b.w;
    }
    // Text/Bytes are OBJ_SLICE (OBJ_TEXT is legacy): compare by length then bytes.
    uint8_t ka = HEADER(as_ptr(a))->kind;
    if (ka != HEADER(as_ptr(b))->kind) {
        return false;
    }
    if (ka == OBJ_SLICE || ka == OBJ_TEXT) {
        size_t na = slice_len(a), nb = slice_len(b);
        return na == nb && memcmp(slice_ptr(a), slice_ptr(b), na) == 0;
    }
    // Boxed floats compare by their double value (so `-0.0 == 0.0`, `NaN != NaN`),
    // which is what an `Eq Float` witness recursing to `=` on a Float leaf expects.
    if (ka == OBJ_FLOAT) {
        return as_float(a) == as_float(b);
    }
    return false;
}

// `prim_show` is monomorphised: codegen selects one of these leaves from the
// argument's static type. Each renders a single primitive value to an owned Text;
// compound values never reach here -- their `Display` witnesses recurse through the
// leaves. (This mirrors the interpreter's `Val` Display, the reference the `expected`
// files are generated from.)
Value prim_show_int(Value x) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%lld", (long long)as_int(x));
    return mk_textn(buf, (size_t)n);
}

// Render a double the way the interpreter's Rust `{:?}` does: the shortest decimal
// that round-trips, always carrying a decimal point (so `1.0` never prints as `1`).
// C has no shortest-round-trip primitive, so grow `%g` precision until the string
// parses back to the same bits, then append `.0` if the result looks integral.
Value prim_show_float(Value x) {
    double d = as_float(x);
    char buf[64];
    int n = 0;
    for (int prec = 1; prec <= 17; prec++) {
        n = snprintf(buf, sizeof buf, "%.*g", prec, d);
        if (strtod(buf, NULL) == d) break; // shortest precision that round-trips
    }
    // `%g` drops the point for integral magnitudes ("1", "100"); restore it so the
    // value reads back as a Float. `nan`/`inf` already contain a letter, so skip them.
    if (!strpbrk(buf, ".eEnN") && n >= 0 && n < (int)sizeof buf - 3) {
        buf[n++] = '.';
        buf[n++] = '0';
        buf[n] = '\0';
    }
    return mk_textn(buf, (size_t)n);
}

Value prim_show_char(Value x) {
    char c = as_char(x);
    return mk_textn(&c, 1);
}

// Display of a Text is the Text itself -- immutable OBJ_SLICE, so returning it is a
// zero-copy identity.
Value prim_show_text(Value x) { return x; }

Value prim_print_endline(Value x) {
    // Text is an OBJ_SLICE with an explicit length (no NUL); write exactly its bytes.
    fwrite(slice_ptr(x), 1, slice_len(x), stdout);
    fputc('\n', stdout);
    return VUnit();
}

Value prim_str_concat(size_t n, ...) {
    // Each part is a Text (OBJ_SLICE). Gather (base, len) pairs, assemble the bytes into
    // a plain malloc buffer, then hand it to `mk_textn` (which builds a fresh Text-slice).
    // Doing all the reads before any allocation keeps the source slice pointers valid.
    const uint8_t **parts = malloc(n * sizeof *parts);
    size_t *lens = malloc(n * sizeof *lens);
    size_t total = 0;
    va_list ap;
    va_start(ap, n);
    for (size_t i = 0; i < n; i++) {
        Value v = va_arg(ap, Value);
        parts[i] = slice_ptr(v);
        lens[i] = slice_len(v);
        total += lens[i];
    }
    va_end(ap);

    char *buf = malloc(total ? total : 1);
    size_t offset = 0;
    for (size_t i = 0; i < n; i++) {
        memcpy(buf + offset, parts[i], lens[i]);
        offset += lens[i];
    }
    free(parts);
    free(lens);
    // `buf` is fully assembled before this point, so the collection that
    // `mk_textn` may trigger cannot disturb it (it is a malloc, not a GC object).
    Value result = mk_textn(buf, total);
    free(buf);
    return result;
}

Value match_fail(void) {
    fprintf(stderr, "runtime error: non-exhaustive deconstruct\n");
    exit(1);
}

BINOP(builtin_add, prim_add);
BINOP(builtin_sub, prim_sub);
BINOP(builtin_mul, prim_mul);
BINOP(builtin_div, prim_div);
BINOP(builtin_mod, prim_mod);
BINOP(builtin_eq, prim_eq);
BINOP(builtin_lt, prim_lt);
BINOP(builtin_gt, prim_gt);
BINOP(builtin_le, prim_le);
BINOP(builtin_ge, prim_ge);
BINOP(builtin_and, prim_and);
BINOP(builtin_or, prim_or);
BINOP(builtin_xor, prim_xor);

UNOP(builtin_not, prim_not);
UNOP(builtin_neg, prim_neg);
UNOP(builtin_int_of_char, prim_int_of_char);
UNOP(builtin_float_of_int, prim_float_of_int);
UNOP(builtin_int_of_float, prim_int_of_float);
UNOP(builtin_char_of_byte, prim_char_of_byte);
UNOP(builtin_print_endline, prim_print_endline);

// text_fold_right : (Char -> a -> a) -> a -> Text -> a
static Value tfr_3(Value self, Value s) {
    Value f = env_get(self, 0);
    Value acc = env_get(self, 1);
    // Text is an OBJ_SLICE; fold right over its bytes. `s` is a live stack Value, so its
    // owner survives the `apply` collections -- re-read each byte via `slice_get_u8`.
    // (Byte-granular for now, matching the previous behaviour; a UTF-8-decoding fold is
    // the later native fast-path.)
    for (size_t k = slice_len(s); k-- > 0;) {
        acc = apply(apply(f, VChar(slice_get_u8(s, k))), acc);
    }
    return acc;
}
static Value tfr_2(Value self, Value z) {
    Value f = env_get(self, 0);
    return mk_closure(tfr_3, 2, f, z);
}
static Value tfr_1(Value self, Value f) {
    (void)self;
    return mk_closure(tfr_2, 1, f);
}
Value builtin_text_fold_right;

void runtime_init(void) {
    builtin_add = mk_closure(builtin_add_1, 0);
    builtin_sub = mk_closure(builtin_sub_1, 0);
    builtin_mul = mk_closure(builtin_mul_1, 0);
    builtin_div = mk_closure(builtin_div_1, 0);
    builtin_mod = mk_closure(builtin_mod_1, 0);
    builtin_eq = mk_closure(builtin_eq_1, 0);
    builtin_lt = mk_closure(builtin_lt_1, 0);
    builtin_gt = mk_closure(builtin_gt_1, 0);
    builtin_le = mk_closure(builtin_le_1, 0);
    builtin_ge = mk_closure(builtin_ge_1, 0);
    builtin_and = mk_closure(builtin_and_1, 0);
    builtin_or = mk_closure(builtin_or_1, 0);
    builtin_xor = mk_closure(builtin_xor_1, 0);
    builtin_not = mk_closure(builtin_not_1, 0);
    builtin_neg = mk_closure(builtin_neg_1, 0);
    builtin_int_of_char = mk_closure(builtin_int_of_char_1, 0);
    builtin_float_of_int = mk_closure(builtin_float_of_int_1, 0);
    builtin_int_of_float = mk_closure(builtin_int_of_float_1, 0);
    builtin_char_of_byte = mk_closure(builtin_char_of_byte_1, 0);
    builtin_print_endline = mk_closure(builtin_print_endline_1, 0);
    builtin_text_fold_right = mk_closure(tfr_1, 0);
}
