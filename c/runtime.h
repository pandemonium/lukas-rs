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
typedef struct Data Data;

// A Marmelade value is a single tagged 64-bit word. The low 3 bits discriminate:
//
//   xxx0   pointer to a heap body -- its kind (closure/tuple/data/text/object)
//          is recovered from the body's `GcHeader.kind`. Bodies are >= 8-byte
//          aligned, so a real pointer always has its low 3 bits clear.
//   x001   Int   -- 61-bit signed, stored as `(n << 3) | 1`
//   x011   Bool  -- `(b << 3) | 3`
//   x101   Char  -- `(c << 3) | 5`
//   x111   Unit  -- the constant 7
//
// Every immediate is odd; every pointer is even, so `w & 1` alone tells them
// apart. Keeping `Value` register-sized (one word, returned in one register) is
// what lets clang sibling-call-optimise the recursive `apply` that loop fusion
// buries -- a 16-byte struct return blocks that TCO and overflows the stack.
// See notes/tagged-value.md.
struct Value {
    uint64_t w;
};

// Low-3-bit immediate tags (`w & TAGMASK` for an odd word).
#define TAGMASK  7u
#define IMM_INT  1u
#define IMM_BOOL 3u
#define IMM_CHAR 5u
#define IMM_UNIT 7u

// The logical kind of a value, for the runtime's own dispatch (`val_eq`,
// `prim_show`). Immediates decode from the low bits; for a pointer the kind
// comes from the heap header, so `value_tag` lives in gc.c where that header is
// visible. Codegen never sees this enum -- it calls typed accessors directly.
typedef enum {
    TAG_INT,
    TAG_TEXT,
    TAG_BOOL,
    TAG_UNIT,
    TAG_CHAR,
    TAG_CLOSURE,
    TAG_TUPLE,
    TAG_DATA,
    TAG_OBJECT, // a GC object (Buffer/Mmap/Slice); GcHeader.kind selects its layout + tracing
} Tag;
Tag value_tag(Value v);

struct Closure {
    Value (*code)(Value self, Value arg);
    // Uncurried fast-path entry for a multi-stage curried chain. When `worker`
    // is non-NULL, this closure is the head of a chain of `arity` stages and
    // `worker(self, args)` runs all of them at once, given exactly `arity`
    // arguments -- skipping the intermediate currying-stage closures that
    // `code` would allocate one per stage. NULL (with arity 1) for an ordinary
    // single-stage closure, which is applied through `code` alone.
    Value (*worker)(Value self, Value *args);
    size_t arity;
    // The captured values are stored *inline* here (a "flat" closure) rather
    // than in a separate environment tuple: one heap object per closure instead
    // of two, and `env_get` is a single load. `nfree` is how many follow, so the
    // collector knows how much of `caps` to trace.
    size_t nfree;
    Value caps[]; // flexible array member
};

struct Tuple {
    size_t len;
    Value elems[]; // flexible array member
};

// A constructor value of a sum type: a small integer `tag` (the constructor's
// ordinal within its type -- unique among that type's constructors, which is all
// a `deconstruct` ever tests) followed by its fields inline. This is leaner than
// a tuple with a string-named tag in slot 0: no 16-byte tag slot, and pattern
// matching compares an integer instead of running `strcmp`. The field count is
// not stored -- it is recovered from the GC header's body size when needed (GC
// tracing, `show`); see `data_len`.
struct Data {
    uint64_t tag;
    Value fields[]; // flexible array member
};

// Owned (heap) text. Declared here so `VText` can build one; defined in gc.c.
// In this stage every text literal is copied to the heap on construction (the
// borrowed-literal optimisation is Stage 1b -- see notes/tagged-value.md).
Value mk_text(const char *src);

// Value constructors. Immediates pack into the word; a text literal becomes an
// owned heap string; `VObject` just carries the (already 8-aligned) body pointer.
static inline Value VInt(int64_t x)     { return (Value){((uint64_t)x << 3) | IMM_INT}; }
static inline Value VText(const char *s){ return mk_text(s); }
static inline Value VBool(bool x)       { return (Value){((uint64_t)(x ? 1u : 0u) << 3) | IMM_BOOL}; }
static inline Value VChar(char x)       { return (Value){((uint64_t)(uint8_t)x << 3) | IMM_CHAR}; }
static inline Value VUnit_(void)        { return (Value){IMM_UNIT}; }
#define VUnit() (VUnit_())
static inline Value VObject(void *p)    { return (Value){(uint64_t)(uintptr_t)p}; }

// Immediate decoders. `as_int` sign-extends via an arithmetic right shift.
static inline int64_t as_int(Value v)  { return (int64_t)v.w >> 3; }
static inline bool    as_bool(Value v) { return (v.w >> 3) & 1u; } // truthiness, for `if`
static inline char    as_char(Value v) { return (char)((v.w >> 3) & 0xFFu); }

// Pointer decoders. A pointer value's word *is* the body pointer.
static inline void     *as_ptr(Value v)     { return (void *)(uintptr_t)v.w; }
static inline Closure  *as_closure(Value v) { return (Closure *)(uintptr_t)v.w; }
static inline Tuple    *as_tuple(Value v)   { return (Tuple *)(uintptr_t)v.w; }
static inline Data     *as_data(Value v)    { return (Data *)(uintptr_t)v.w; }
static inline const char *as_text(Value v)  { return (const char *)(uintptr_t)v.w; }

// Primitive operations behind the builtins. Codegen emits direct calls to these
// for *saturated* applications, bypassing the curried closures (and their heap
// allocation) entirely. The `builtin_*` closure values below remain for partial
// application and higher-order use (e.g. passing `+` to a fold).
bool val_eq(Value a, Value b);
// Arithmetic is untag -> compute -> retag. Int is 61-bit, so overflow wraps
// (OCaml-style, no check); the codec's fields fit, full-width lands in Stage 2.
static inline Value prim_add(Value a, Value b) { return VInt(as_int(a) + as_int(b)); }
static inline Value prim_sub(Value a, Value b) { return VInt(as_int(a) - as_int(b)); }
static inline Value prim_mul(Value a, Value b) { return VInt(as_int(a) * as_int(b)); }
static inline Value prim_div(Value a, Value b) { return VInt(as_int(a) / as_int(b)); }
static inline Value prim_mod(Value a, Value b) { return VInt(as_int(a) % as_int(b)); }
static inline Value prim_lt(Value a, Value b) { return VBool(as_int(a) < as_int(b)); }
static inline Value prim_gt(Value a, Value b) { return VBool(as_int(a) > as_int(b)); }
static inline Value prim_le(Value a, Value b) { return VBool(as_int(a) <= as_int(b)); }
static inline Value prim_ge(Value a, Value b) { return VBool(as_int(a) >= as_int(b)); }
static inline Value prim_eq(Value a, Value b) { return VBool(val_eq(a, b)); }
static inline Value prim_and(Value a, Value b) { return VBool(as_bool(a) && as_bool(b)); }
static inline Value prim_or(Value a, Value b) { return VBool(as_bool(a) || as_bool(b)); }
static inline Value prim_xor(Value a, Value b) { return VBool(as_bool(a) != as_bool(b)); }
Value prim_show(Value x);
Value prim_print_endline(Value x);
// Concatenate `n` text values (used by string interpolation).
Value prim_str_concat(size_t n, ...);

// The heap constructors (`mk_closure`/`mk_tuple`) and the collector API live in
// gc.h, since they are what the garbage collector manages.

// Apply a closure value to an argument.
static inline Value apply(Value f, Value x) { return as_closure(f)->code(f, x); }

// Apply a closure value to `n` arguments at once (the flattened spine of a
// nested application). When `f` is the head of a curried chain whose remaining
// arity is exactly `n` and it carries an uncurried `worker`, dispatch straight
// to the worker -- no intermediate currying-stage closures are allocated. Every
// other shape (no worker, partial application `n < arity`, over-application
// `n > arity`, or a plain single-stage closure) falls back to applying one
// argument at a time through `code`, exactly reproducing the curried semantics.
static inline Value apply_n(Value f, size_t n, Value *args) {
    Closure *c = as_closure(f);
    if (c->worker && c->arity == n) {
        return c->worker(f, args);
    }
    Value r = f;
    for (size_t i = 0; i < n; i++) {
        r = apply(r, args[i]);
    }
    return r;
}

// i-th element of a tuple value (also used for record ordinals).
static inline Value proj(Value t, size_t i) { return as_tuple(t)->elems[i]; }

// A constructor value's tag (which constructor) and i-th field. Codegen knows
// statically whether a value is a tuple or a constructor -- tuple/record access
// uses `proj`, constructor access uses these -- so no runtime tag check here.
#define data_tag(v) (as_data(v)->tag)
#define data_field(v, i) (as_data(v)->fields[(i)])

// i-th captured value, read out of a closure's own (inline) environment.
#define env_get(self, i) (as_closure(self)->caps[(i)])

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
#define unbox_int64_t(v) (as_int(v))
#define box_int64_t(x) VInt(x)

#define CTYPE_Bool bool
#define unbox_Bool(v) (as_bool(v))
#define box_Bool(x) VBool(x)

#define CTYPE_Char char
#define unbox_Char(v) (as_char(v))
#define box_Char(x) VChar(x)

#define CTYPE_Text const char *
#define unbox_Text(v) (as_text(v))
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
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

// Arity 2: stage 1 captures the first argument, stage 2 applies the body.
#define FOREIGN_DECL_2(RET, NAME, T1, A1, T2, A2, BODY)                                \
    static CTYPE_##RET NAME##_impl(CTYPE_##T1 A1, CTYPE_##T2 A2) BODY                  \
    static Value NAME##_stage2(Value self, Value a2v) {                                \
        return box_##RET(NAME##_impl(unbox_##T1(env_get(self, 0)), unbox_##T2(a2v)));  \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value a1v) {                                \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, 1, a1v);                                      \
    }                                                                                  \
    Value NAME##_worker(Value a1, Value a2) {                                          \
        return box_##RET(NAME##_impl(unbox_##T1(a1), unbox_##T2(a2)));                 \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

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
        return mk_closure(NAME##_stage3, 2, env_get(self, 0), av);           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, 1, av);                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

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
        return mk_closure(NAME##_stage4, 3, env_get(self, 0),                          \
                                         env_get(self, 1), av);                        \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, 2, env_get(self, 0), av);           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, 1, av);                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

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
                          4, env_get(self, 0), env_get(self, 1),                       \
                                   env_get(self, 2), av);                              \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage4, 3, env_get(self, 0),                          \
                                         env_get(self, 1), av);                        \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, 2, env_get(self, 0), av);           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, 1, av);                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

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
                          5, env_get(self, 0), env_get(self, 1),                       \
                                   env_get(self, 2), env_get(self, 3), av);            \
    }                                                                                  \
    static Value NAME##_stage4(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage5,                                               \
                          4, env_get(self, 0), env_get(self, 1),                       \
                                   env_get(self, 2), av);                              \
    }                                                                                  \
    static Value NAME##_stage3(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage4, 3, env_get(self, 0),                          \
                                         env_get(self, 1), av);                        \
    }                                                                                  \
    static Value NAME##_stage2(Value self, Value av) {                                 \
        return mk_closure(NAME##_stage3, 2, env_get(self, 0), av);           \
    }                                                                                  \
    static Value NAME##_stage1(Value self, Value av) {                                 \
        (void)self;                                                                    \
        return mk_closure(NAME##_stage2, 1, av);                             \
    }                                                                                  \
    Value NAME;                                                                        \
    Value NAME##__init(void) { return mk_closure(NAME##_stage1, 0); }

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
