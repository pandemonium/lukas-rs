// C runtime for the Marmelade C backend.
//
// Every Marmelade value is one `Value` -- a small tagged union. This is the
// uniform, boxed representation: it sidesteps monomorphising the language's
// real polymorphism (`prim_show`, `=`, `id`, dictionaries) by making every
// term the same C type. Closures carry themselves: a lifted function has the
// signature `Value code(Value self, Value arg)`, so `self` gives it both its
// captured environment (`env_get`) and, for recursion, itself (`SelfRef`).
//
// Heap values -- closures, tuples, and owned strings -- are managed by the
// collector in gc.c and reclaimed when unreachable. String *literals* are the
// exception: they are borrowed pointers into read-only data (`VText("...")`),
// never heap objects, so they are never collected (nor need to be). Owned
// strings come from `mk_text`/`mk_textn` (see gc.h).
#ifndef MARMELADE_RUNTIME_H
#define MARMELADE_RUNTIME_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct Value Value;
typedef struct Closure Closure;
typedef struct Tuple Tuple;

typedef enum {
    TAG_INT,
    TAG_TEXT,
    TAG_BOOL,
    TAG_UNIT,
    TAG_CHAR,
    TAG_CLOSURE,
    TAG_TUPLE,
} Tag;

struct Value {
    Tag tag;
    union {
        int64_t i;
        const char *s;
        bool b;
        char c;
        Closure *clo;
        Tuple *tup;
    };
};

struct Closure {
    Value (*code)(Value self, Value arg);
    Value env; // a TAG_TUPLE Value holding the captured values
};

struct Tuple {
    size_t len;
    Value elems[]; // flexible array member
};

// Value constructors.
static inline Value VInt(int64_t x)     { Value v; v.tag = TAG_INT;  v.i = x; return v; }
static inline Value VText(const char *s){ Value v; v.tag = TAG_TEXT; v.s = s; return v; }
static inline Value VBool(bool x)       { Value v; v.tag = TAG_BOOL; v.b = x; return v; }
static inline Value VChar(char x)       { Value v; v.tag = TAG_CHAR; v.c = x; return v; }
static inline Value VUnit_(void)        { Value v; v.tag = TAG_UNIT; v.i = 0; return v; }
#define VUnit() (VUnit_())

// Truthiness of a Bool value, for `if`.
static inline bool as_bool(Value v) { return v.b; }

// Primitive operations behind the builtins. Codegen emits direct calls to these
// for *saturated* applications, bypassing the curried closures (and their heap
// allocation) entirely. The `builtin_*` closure values below remain for partial
// application and higher-order use (e.g. passing `+` to a fold).
bool val_eq(Value a, Value b);
static inline Value prim_add(Value a, Value b) { return VInt(a.i + b.i); }
static inline Value prim_sub(Value a, Value b) { return VInt(a.i - b.i); }
static inline Value prim_mul(Value a, Value b) { return VInt(a.i * b.i); }
static inline Value prim_div(Value a, Value b) { return VInt(a.i / b.i); }
static inline Value prim_mod(Value a, Value b) { return VInt(a.i % b.i); }
static inline Value prim_lt(Value a, Value b) { return VBool(a.i < b.i); }
static inline Value prim_gt(Value a, Value b) { return VBool(a.i > b.i); }
static inline Value prim_le(Value a, Value b) { return VBool(a.i <= b.i); }
static inline Value prim_ge(Value a, Value b) { return VBool(a.i >= b.i); }
static inline Value prim_eq(Value a, Value b) { return VBool(val_eq(a, b)); }
static inline Value prim_and(Value a, Value b) { return VBool(a.b && b.b); }
static inline Value prim_or(Value a, Value b) { return VBool(a.b || b.b); }
static inline Value prim_xor(Value a, Value b) { return VBool(a.b != b.b); }
Value prim_show(Value x);
Value prim_print_endline(Value x);
// Concatenate `n` text values (used by string interpolation).
Value prim_str_concat(size_t n, ...);

// The heap constructors (`mk_closure`/`mk_tuple`) and the collector API live in
// gc.h, since they are what the garbage collector manages.

// Apply a closure value to an argument.
static inline Value apply(Value f, Value x) { return f.clo->code(f, x); }

// i-th element of a tuple value (also used for record ordinals).
static inline Value proj(Value t, size_t i) { return t.tup->elems[i]; }

// i-th captured value, read out of a closure's own environment.
#define env_get(self, i) ((self).clo->env.tup->elems[(i)])

// Aborts on a non-exhaustive `deconstruct`. Returns Value only so it can sit in
// the tail of a ternary chain; it never actually returns.
Value match_fail(void);

// Builtins, provided as curried closure values. `runtime_init` fills them in.
void runtime_init(void);

extern Value builtin_add;
extern Value builtin_sub;
extern Value builtin_mul;
extern Value builtin_div;
extern Value builtin_mod;
extern Value builtin_eq;
extern Value builtin_lt;
extern Value builtin_gt;
extern Value builtin_le;
extern Value builtin_ge;
extern Value builtin_and;
extern Value builtin_or;
extern Value builtin_xor;
extern Value builtin_show;
extern Value builtin_print_endline;
extern Value builtin_text_fold_right;

// --------------------------------------------------------------- foreign functions
// A `foreign f :: T` declaration in a Marmelade module `M` is implemented in a
// companion `M.c` with the `FOREIGN_DECL` macro. The compiler emits the matching
// global, its initialiser call, and its GC root; the macro supplies the curried
// closure and the marshalling to/from the boxed `Value`.
//
//   FOREIGN_DECL(ret_tag, M_f, arg_tag, name, ..., { C body returning ret })
//
// Arguments: the return type tag, the (mangled) function name `Module_member`,
// then a `type_tag, name` pair per parameter (0 through 6 supported), then a C
// function body operating on the *unmarshalled* C values. Example:
//
//   FOREIGN_DECL(int64_t, Root_pow, int64_t, base, int64_t, exp, {
//       int64_t acc = 1;
//       while (exp-- > 0) acc *= base;
//       return acc;
//   })
//
// A tag names a C type plus a `box`/`unbox` conversion pair -- `box_<tag>` builds
// a `Value` from a C value (used on the return), `unbox_<tag>` reads a C value
// back out (used on each argument). `Value` is the escape hatch (no marshalling)
// for anything the built-in tags don't cover. Add a tag by defining its three
// macros: `CTYPE_<tag>`, `box_<tag>`, `unbox_<tag>`.
#define CTYPE_int64_t int64_t
#define unbox_int64_t(v) ((v).i)
#define box_int64_t(x) VInt(x)

#define CTYPE_Bool bool
#define unbox_Bool(v) ((v).b)
#define box_Bool(x) VBool(x)

#define CTYPE_Char char
#define unbox_Char(v) ((v).c)
#define box_Char(x) VChar(x)

#define CTYPE_Text const char *
#define unbox_Text(v) ((v).s)
// Copy the returned C string into a collectable heap text: a foreign function
// hands back a *borrowed* pointer (a stack or static buffer), never ownership of
// a malloc. `mk_text` takes the owning copy the collector then manages.
#define box_Text(x) mk_text(x)

#define CTYPE_Value Value
#define unbox_Value(v) (v)
#define box_Value(x) (x)

// Arity 0: a foreign constant. `NAME__init` computes the value once at startup.
#define FOREIGN_DECL_0(RET, NAME, BODY)                                                \
    static CTYPE_##RET NAME##_impl(void) BODY                                          \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return box_##RET(NAME##_impl()); }

// Arity 1: one closure stage forwards straight to the body.
#define FOREIGN_DECL_1(RET, NAME, T1, A1, BODY)                                        \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1) BODY                                 \
    static Value NAME##_stage1(Value self, Value a1v) {                                \
        (void)self;                                                                    \
        return box_##RET(NAME##_impl(unbox_##T1(a1v)));                                \
    }                                                                                  \
    Value NAME##_worker(Value a1) { return box_##RET(NAME##_impl(unbox_##T1(a1))); }   \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

// Arity 2: stage 1 captures the first argument, stage 2 applies the body.
#define FOREIGN_DECL_2(RET, NAME, T1, A1, T2, A2, BODY)                                \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2) BODY                  \
    static Value NAME##_stage2(Value self, Value a2v) {                                \
        return box_##RET(NAME##_impl(unbox_##T1(env_get(self, 0)), unbox_##T2(a2v)));  \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value a1v) {                                \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, mk_tuple(1, a1v));                            \
    }                                                                                  \
    Value NAME##_worker(Value a1, Value a2) {                                          \
        return box_##RET(NAME##_impl(unbox_##T1(a1), unbox_##T2(a2)));                 \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

// Arities 3-6 follow the same shape: each stage k<N captures the arguments so
// far (rebuilding the environment tuple) and returns the next stage; the final
// stage unmarshals the whole environment plus the last argument and calls the
// body. Higher arities are a mechanical continuation of this pattern.
#define FOREIGN_DECL_3(RET, NAME, T1, A1, T2, A2, T3, A3, BODY)                        \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2, CTYPE_##T3 A3)        \
        BODY                                                                           \
    Value NAME##_worker(Value a1, Value a2, Value a3) {                                \
        return box_##RET(                                                              \
            NAME##_impl(unbox_##T1(a1), unbox_##T2(a2), unbox_##T3(a3)));              \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return box_##RET(NAME##_impl(unbox_##T1(env_get(self, 0)),                     \
                                    unbox_##T2(env_get(self, 1)), unbox_##T3(av)));    \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, mk_tuple(2, env_get(self, 0), av));           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, mk_tuple(1, av));                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

#define FOREIGN_DECL_4(RET, NAME, T1, A1, T2, A2, T3, A3, T4, A4, BODY)                \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2,                       \
                                   CTYPE_##T3 A3, CTYPE_##T4 A4) BODY                  \
    Value NAME##_worker(Value a1, Value a2, Value a3, Value a4) {                      \
        return box_##RET(NAME##_impl(unbox_##T1(a1), unbox_##T2(a2),                   \
                                     unbox_##T3(a3), unbox_##T4(a4)));                 \
    }                                                                                  \
    static Value NAME##_stage4(Value self, Value av) {                                 \
        return box_##RET(NAME##_impl(                                                  \
            unbox_##T1(env_get(self, 0)), unbox_##T2(env_get(self, 1)),                \
            unbox_##T3(env_get(self, 2)), unbox_##T4(av)));                            \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage4, mk_tuple(3, env_get(self, 0),                 \
                                                  env_get(self, 1), av));              \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, mk_tuple(2, env_get(self, 0), av));           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, mk_tuple(1, av));                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

#define FOREIGN_DECL_5(RET, NAME, T1, A1, T2, A2, T3, A3, T4, A4, T5, A5,              \
                       BODY)                                                           \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2, CTYPE_##T3 A3,        \
                                   CTYPE_##T4 A4, CTYPE_##T5 A5) BODY                  \
    Value NAME##_worker(Value a1, Value a2, Value a3, Value a4, Value a5) {            \
        return box_##RET(NAME##_impl(unbox_##T1(a1), unbox_##T2(a2), unbox_##T3(a3),   \
                                     unbox_##T4(a4), unbox_##T5(a5)));                 \
    }                                                                                  \
    static Value NAME##_stage5(Value self, Value av) {                                 \
        return box_##RET(NAME##_impl(                                                  \
            unbox_##T1(env_get(self, 0)), unbox_##T2(env_get(self, 1)),                \
            unbox_##T3(env_get(self, 2)), unbox_##T4(env_get(self, 3)),                \
            unbox_##T5(av)));                                                          \
    }                                                                                  \
    static Value NAME##_stage4(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage5,                                               \
                          mk_tuple(4, env_get(self, 0), env_get(self, 1),              \
                                   env_get(self, 2), av));                             \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage4, mk_tuple(3, env_get(self, 0),                 \
                                                  env_get(self, 1), av));              \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, mk_tuple(2, env_get(self, 0), av));           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, mk_tuple(1, av));                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

#define FOREIGN_DECL_6(RET, NAME, T1, A1, T2, A2, T3, A3, T4, A4, T5, A5, T6,          \
                       A6, BODY)                                                       \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2, CTYPE_##T3 A3,        \
                                   CTYPE_##T4 A4, CTYPE_##T5 A5, CTYPE_##T6 A6)        \
        BODY                                                                           \
    Value NAME##_worker(Value a1, Value a2, Value a3, Value a4, Value a5, Value a6) {  \
        return box_##RET(NAME##_impl(unbox_##T1(a1), unbox_##T2(a2), unbox_##T3(a3),   \
                                     unbox_##T4(a4), unbox_##T5(a5), unbox_##T6(a6))); \
    }                                                                                  \
    static Value NAME##_stage6(Value self, Value av) {                                 \
        return box_##RET(NAME##_impl(                                                  \
            unbox_##T1(env_get(self, 0)), unbox_##T2(env_get(self, 1)),                \
            unbox_##T3(env_get(self, 2)), unbox_##T4(env_get(self, 3)),                \
            unbox_##T5(env_get(self, 4)), unbox_##T6(av)));                            \
    }                                                                                  \
    static Value NAME##_stage5(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage6,                                               \
                          mk_tuple(5, env_get(self, 0), env_get(self, 1),              \
                                   env_get(self, 2), env_get(self, 3), av));           \
    }                                                                                  \
    static Value NAME##_stage4(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage5,                                               \
                          mk_tuple(4, env_get(self, 0), env_get(self, 1),              \
                                   env_get(self, 2), av));                             \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage4, mk_tuple(3, env_get(self, 0),                 \
                                                  env_get(self, 1), av));              \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, mk_tuple(2, env_get(self, 0), av));           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, mk_tuple(1, av));                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, mk_tuple(0)); }

// Dispatch on argument count: the body is a single (final) argument, so a valid
// call has 3, 5, 7, 9, 11, 13, or 15 arguments -> arity 0..6. Anything else
// (an even count, or arity > 6) fails to match cleanly and is a compile error.
#define FD_BADARITY(...)                                                               \
    _Static_assert(0, "FOREIGN_DECL: expected (ret, name[, type, param]..., body), arity 0-6")
#define FD_GET(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14,            \
               _15, MACRO, ...)                                                        \
    MACRO
#define FOREIGN_DECL(...)                                                              \
    FD_GET(__VA_ARGS__, FOREIGN_DECL_6, FD_BADARITY, FOREIGN_DECL_5,                   \
           FD_BADARITY, FOREIGN_DECL_4, FD_BADARITY, FOREIGN_DECL_3,                   \
           FD_BADARITY, FOREIGN_DECL_2, FD_BADARITY, FOREIGN_DECL_1,                   \
           FD_BADARITY, FOREIGN_DECL_0, FD_BADARITY, FD_BADARITY)                      \
    (__VA_ARGS__)

#endif // MARMELADE_RUNTIME_H
