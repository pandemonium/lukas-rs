// C runtime for the Marmelade C backend.
//
// Every Marmelade value is one `Value` -- a small tagged union. This is the
// uniform, boxed representation: it sidesteps monomorphising the language's
// real polymorphism (`prim_show`, `=`, `id`, dictionaries) by making every
// term the same C type. Closures carry themselves: a lifted function has the
// signature `Value code(Value self, Value arg)`, so `self` gives it both its
// captured environment (`env_get`) and, for recursion, itself (`SelfRef`).
//
// Memory is currently leaked (plain malloc, no free). A collector can be added
// later without changing the emitted code.
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

// Heap constructors (defined in runtime.c).
Value mk_closure(Value (*code)(Value, Value), Value env);
Value mk_tuple(size_t len, ...);

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

#endif // MARMELADE_RUNTIME_H
