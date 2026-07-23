#include "runtime.h"

#include "gc.h" // mk_closure / mk_tuple

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
    Tag ta = value_tag(a);
    if (ta != value_tag(b)) {
        return false;
    }
    switch (ta) {
    case TAG_INT:  return as_int(a) == as_int(b);
    case TAG_BOOL: return as_bool(a) == as_bool(b);
    case TAG_CHAR: return as_char(a) == as_char(b);
    case TAG_TEXT: return strcmp(as_text(a), as_text(b)) == 0;
    case TAG_UNIT: return true;
    default:       return false;
    }
}

// Render a value to a freshly malloc'd C string, mirroring the interpreter's
// `Val` Display (the reference the `expected` files are generated from).
static char *show_alloc(Value x);

// A product (tuple or record) prints as `(e0, e1, …)`: elements comma-separated
// and parenthesised, so nesting stays visible -- `((1, 2), 3)` rather than the
// flat `1, 2, 3`. NB: constructor values share the TAG_TUPLE layout (name in
// slot 0), so they too print in this shape -- see the note in prim_show.
static char *show_tuple(Tuple *t) {
    size_t n = t->len;
    char **parts = malloc(n * sizeof *parts);
    size_t total = 3; // '(' + ')' + '\0'
    for (size_t i = 0; i < n; i++) {
        parts[i] = show_alloc(t->elems[i]);
        total += strlen(parts[i]) + (i ? 2 : 0); // ", " between elements
    }

    char *out = malloc(total);
    char *p = out;
    *p++ = '(';
    for (size_t i = 0; i < n; i++) {
        if (i) {
            *p++ = ',';
            *p++ = ' ';
        }
        size_t len = strlen(parts[i]);
        memcpy(p, parts[i], len);
        p += len;
        free(parts[i]);
    }
    *p++ = ')';
    *p = '\0';
    free(parts);
    return out;
}

// A constructor value prints as `#<tag>(fields…)` (or just `#<tag>` for a
// nullary constructor). The runtime carries no constructor *names*, only the
// integer tag, so `show` of a data value is a debugging aid rather than
// source-faithful -- the previous string-tag layout printed the mangled name,
// but nothing depends on that.
static char *show_data(Value x) {
    size_t n = data_len(x);
    char tagbuf[24];
    snprintf(tagbuf, sizeof tagbuf, "#%llu", (unsigned long long)data_tag(x));
    if (n == 0) {
        return strdup(tagbuf);
    }
    char **parts = malloc(n * sizeof *parts);
    size_t total = strlen(tagbuf) + 3; // "(" + ")" + '\0'
    for (size_t i = 0; i < n; i++) {
        parts[i] = show_alloc(data_field(x, i));
        total += strlen(parts[i]) + (i ? 2 : 0); // ", " between fields
    }
    char *out = malloc(total);
    char *p = out;
    size_t tlen = strlen(tagbuf);
    memcpy(p, tagbuf, tlen);
    p += tlen;
    *p++ = '(';
    for (size_t i = 0; i < n; i++) {
        if (i) {
            *p++ = ',';
            *p++ = ' ';
        }
        size_t len = strlen(parts[i]);
        memcpy(p, parts[i], len);
        p += len;
        free(parts[i]);
    }
    *p++ = ')';
    *p = '\0';
    free(parts);
    return out;
}

static char *show_alloc(Value x) {
    char buf[32];
    switch (value_tag(x)) {
    case TAG_INT:
        snprintf(buf, sizeof buf, "%lld", (long long)as_int(x));
        return strdup(buf);
    case TAG_BOOL:
        return strdup(as_bool(x) ? "true" : "false");
    case TAG_CHAR:
        buf[0] = as_char(x);
        buf[1] = '\0';
        return strdup(buf);
    case TAG_TEXT:
        return strdup(as_text(x));
    case TAG_UNIT:
        return strdup("()");
    case TAG_TUPLE:
        return show_tuple(as_tuple(x));
    case TAG_DATA:
        return show_data(x);
    default:
        return strdup("<value>");
    }
}

// NB: sum-type constructors are TAG_TUPLE with the constructor name in slot 0,
// indistinguishable at runtime from a plain tuple, so `Some 5` currently renders
// as `(Some, 5)` rather than the interpreter's `(Some 5)`. Disambiguating needs
// a representation change (a distinct tag/marker); tuples and records are exact.
Value prim_show(Value x) {
    // `show_alloc` returns a temporary malloc; hand its contents to the collector
    // as an owned text and release the temporary.
    char *s = show_alloc(x);
    Value v = mk_text(s);
    free(s);
    return v;
}

Value prim_print_endline(Value x) {
    fputs(as_text(x), stdout);
    fputc('\n', stdout);
    return VUnit();
}

Value prim_str_concat(size_t n, ...) {
    const char **parts = malloc(n * sizeof *parts);
    size_t total = 0;
    va_list ap;
    va_start(ap, n);
    for (size_t i = 0; i < n; i++) {
        Value v = va_arg(ap, Value);
        parts[i] = as_text(v);
        total += strlen(parts[i]);
    }
    va_end(ap);

    char *buf = malloc(total + 1);
    size_t offset = 0;
    for (size_t i = 0; i < n; i++) {
        size_t len = strlen(parts[i]);
        memcpy(buf + offset, parts[i], len);
        offset += len;
    }
    buf[offset] = '\0';
    free(parts);
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

UNOP(builtin_show, prim_show);
UNOP(builtin_print_endline, prim_print_endline);

// text_fold_right : (Char -> a -> a) -> a -> Text -> a
static Value tfr_3(Value self, Value s) {
    Value f = env_get(self, 0);
    Value acc = env_get(self, 1);
    const char *str = as_text(s);
    for (size_t k = strlen(str); k-- > 0;) {
        acc = apply(apply(f, VChar(str[k])), acc);
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
    builtin_show = mk_closure(builtin_show_1, 0);
    builtin_print_endline = mk_closure(builtin_print_endline_1, 0);
    builtin_text_fold_right = mk_closure(tfr_1, 0);
}
