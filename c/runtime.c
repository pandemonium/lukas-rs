#include "runtime.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

Value mk_closure(Value (*code)(Value, Value), Value env) {
    Closure *c = malloc(sizeof *c);
    c->code = code;
    c->env = env;
    Value v;
    v.tag = TAG_CLOSURE;
    v.clo = c;
    return v;
}

Value mk_tuple(size_t len, ...) {
    Tuple *t = malloc(sizeof *t + len * sizeof(Value));
    t->len = len;
    va_list ap;
    va_start(ap, len);
    for (size_t i = 0; i < len; i++) {
        t->elems[i] = va_arg(ap, Value);
    }
    va_end(ap);
    Value v;
    v.tag = TAG_TUPLE;
    v.tup = t;
    return v;
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
        return mk_closure(NAME##_2, mk_tuple(1, x));                           \
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
    if (a.tag != b.tag) {
        return false;
    }
    switch (a.tag) {
    case TAG_INT:  return a.i == b.i;
    case TAG_BOOL: return a.b == b.b;
    case TAG_CHAR: return a.c == b.c;
    case TAG_TEXT: return strcmp(a.s, b.s) == 0;
    case TAG_UNIT: return true;
    default:       return false;
    }
}

Value prim_show(Value x) {
    char buf[32];
    switch (x.tag) {
    case TAG_INT:
        snprintf(buf, sizeof buf, "%lld", (long long)x.i);
        return VText(strdup(buf));
    case TAG_BOOL:
        return VText(x.b ? "true" : "false");
    case TAG_CHAR:
        buf[0] = x.c;
        buf[1] = '\0';
        return VText(strdup(buf));
    case TAG_TEXT:
        return x;
    case TAG_UNIT:
        return VText("()");
    default:
        return VText("<value>");
    }
}

Value prim_print_endline(Value x) {
    fputs(x.s, stdout);
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
        parts[i] = v.s;
        total += strlen(v.s);
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
    return VText(buf);
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
    const char *str = s.s;
    for (size_t k = strlen(str); k-- > 0;) {
        acc = apply(apply(f, VChar(str[k])), acc);
    }
    return acc;
}
static Value tfr_2(Value self, Value z) {
    Value f = env_get(self, 0);
    return mk_closure(tfr_3, mk_tuple(2, f, z));
}
static Value tfr_1(Value self, Value f) {
    (void)self;
    return mk_closure(tfr_2, mk_tuple(1, f));
}
Value builtin_text_fold_right;

void runtime_init(void) {
    Value empty = mk_tuple(0);
    builtin_add = mk_closure(builtin_add_1, empty);
    builtin_sub = mk_closure(builtin_sub_1, empty);
    builtin_mul = mk_closure(builtin_mul_1, empty);
    builtin_div = mk_closure(builtin_div_1, empty);
    builtin_mod = mk_closure(builtin_mod_1, empty);
    builtin_eq = mk_closure(builtin_eq_1, empty);
    builtin_lt = mk_closure(builtin_lt_1, empty);
    builtin_gt = mk_closure(builtin_gt_1, empty);
    builtin_le = mk_closure(builtin_le_1, empty);
    builtin_ge = mk_closure(builtin_ge_1, empty);
    builtin_and = mk_closure(builtin_and_1, empty);
    builtin_or = mk_closure(builtin_or_1, empty);
    builtin_xor = mk_closure(builtin_xor_1, empty);
    builtin_show = mk_closure(builtin_show_1, empty);
    builtin_print_endline = mk_closure(builtin_print_endline_1, empty);
    builtin_text_fold_right = mk_closure(tfr_1, empty);
}
