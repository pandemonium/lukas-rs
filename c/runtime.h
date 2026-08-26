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

#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct Value Value;
typedef struct Closure Closure;
typedef struct Tuple Tuple;
typedef struct Data Data;

// A Marmelade value is a single tagged 64-bit word. ONE bit discriminates:
//
//   xxx0   pointer to a heap body -- its kind (closure/tuple/data/text/object)
//          is recovered from the body's `GcHeader.kind`. Bodies are >= 8-byte
//          aligned, so a real pointer always has its low bit clear.
//   xxx1   immediate -- Int/Bool/Char/Unit, payload in the high 63 bits
//          (`(payload << 1) | 1`). The word carries NO tag saying *which*
//          immediate it is: access is type-driven (codegen picks `as_int`
//          vs `as_char` from the static type), equality of immediates is word
//          identity (`a.w == b.w`), and `show` is lowered per-type at codegen.
//          Int is therefore 63-bit signed. See notes/tagged-value.md.
//
// Every immediate is odd; every pointer is even, so `w & 1` alone tells them
// apart -- which is all the GC needs to trace heap fields precisely. Keeping
// `Value` register-sized (one word, returned in one register) is what lets clang
// sibling-call-optimise the recursive `apply` that loop fusion buries -- a
// 16-byte struct return blocks that TCO and overflows the stack.
struct Value {
    uint64_t w;
};

// The single immediate tag bit: an odd word is an immediate, an even word a pointer.
#define IMM_TAG 1u

// The per-FUNCTION part of a closure: `code`, `worker`, and `arity` are identical
// for every closure of a given lifted function, so codegen emits ONE static
// descriptor (in .rodata) that all its closures point at, instead of re-storing all
// three (24 B) in each heap closure. `code` is the single-stage entry; `worker` is
// the uncurried fast-path entry for a curried chain of `arity` stages (NULL, arity 1,
// for an ordinary single-stage closure), letting a saturated `apply_n` skip the
// intermediate currying-stage closures.
typedef struct ClosureDesc {
    Value (*code)(Value self, Value arg);
    Value (*worker)(Value self, Value *args);
    size_t arity;
} ClosureDesc;

struct Closure {
    const ClosureDesc *desc; // shared static {code, worker, arity}; per-function, not per-closure
    // The captured values are stored *inline* here (a "flat" closure) rather than in
    // a separate environment tuple: one heap object per closure, and `env_get` is a
    // single load. The capture count is recovered from the GC header's body size
    // (`(body - sizeof(Closure)) / sizeof(Value)`), so it is not stored.
    Value caps[]; // flexible array member
};

struct Tuple {
    // No `len` field: like `Data`, the element count is recovered from the GC
    // header's body size (`body / sizeof(Value)`), saving 8 bytes per tuple. A
    // tuple body is exactly `n * sizeof(Value)`, so the division is exact.
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
    // No `tag` body word: the constructor tag lives in the GC header's `ctag`
    // byte (see gc.h), so a constructor node is 8 B leaner. Fields are inline,
    // exactly like a tuple; the count is recovered from the header body size.
    Value fields[]; // flexible array member
};

// Owned (heap) text. Declared here so `VText` can build one; defined in gc.c.
// In this stage every text literal is copied to the heap on construction (the
// borrowed-literal optimisation is Stage 1b -- see notes/tagged-value.md).
Value mk_text(const char *src);

// Box a double on the heap (OBJ_FLOAT leaf). Defined in gc.c; declared here so `VFloat`
// can build one. A 64-bit float cannot be an immediate, so every computed Float boxes.
Value mk_float(double x);

// Wall-clock time in milliseconds since the Unix epoch. Passed to the program's
// `start` entry point as its argument.
int64_t now_millis(void);

// Value constructors. Immediates pack into the word; a text literal becomes an
// owned heap string; `VObject` just carries the (already 8-aligned) body pointer.
static inline Value VInt(int64_t x)     { return (Value){((uint64_t)x << 1) | IMM_TAG}; }
static inline Value VText(const char *s){ return mk_text(s); }
static inline Value VBool(bool x)       { return (Value){((uint64_t)(x ? 1u : 0u) << 1) | IMM_TAG}; }
static inline Value VChar(char x)       { return (Value){((uint64_t)(uint8_t)x << 1) | IMM_TAG}; }
static inline Value VUnit_(void)        { return (Value){IMM_TAG}; }
#define VUnit() (VUnit_())
static inline Value VObject(void *p)    { return (Value){(uint64_t)(uintptr_t)p}; }
// A Float is a pointer to a heap-boxed double (OBJ_FLOAT); it can never be immediate.
static inline Value VFloat(double x)    { return mk_float(x); }

// Immediate decoders. `as_int` sign-extends via an arithmetic right shift. Each is
// type-driven: codegen calls the right one from the static type -- the word itself
// carries no tag distinguishing Int/Bool/Char/Unit.
static inline int64_t as_int(Value v)  { return (int64_t)v.w >> 1; }
static inline bool    as_bool(Value v) { return (v.w >> 1) & 1u; } // truthiness, for `if`
static inline char    as_char(Value v) { return (char)((v.w >> 1) & 0xFFu); }

// A boxed Float: the word is the OBJ_FLOAT body pointer, which points straight at the
// stored double (the box body is exactly one double). Read it back by value.
static inline double   as_float(Value v)    { return *(const double *)(uintptr_t)v.w; }

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
// Arithmetic is untag -> compute -> retag. Int is 63-bit, so overflow wraps
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
// `and`/`or`/`xor` are logical on Bool (these) and bitwise on Int (the `prim_b*`
// forms below); codegen picks between them on the operands' static type, exactly as
// it picks the Float arithmetic prims.
static inline Value prim_and(Value a, Value b) { return VBool(as_bool(a) && as_bool(b)); }
static inline Value prim_or(Value a, Value b) { return VBool(as_bool(a) || as_bool(b)); }
static inline Value prim_xor(Value a, Value b) { return VBool(as_bool(a) != as_bool(b)); }
static inline Value prim_band(Value a, Value b) { return VInt(as_int(a) & as_int(b)); }
static inline Value prim_bor(Value a, Value b)  { return VInt(as_int(a) | as_int(b)); }
static inline Value prim_bxor(Value a, Value b) { return VInt(as_int(a) ^ as_int(b)); }
// Unary `not`: logical complement on Bool, bitwise complement on Int (codegen picks
// `prim_bnot` when the operand's static type is Int).
static inline Value prim_not(Value a)  { return VBool(!as_bool(a)); }
static inline Value prim_bnot(Value a) { return VInt(~as_int(a)); }
// Unary minus: arithmetic negation. `prim_neg` is Int; codegen picks `prim_fneg`
// (defined with the Float prims below) when the operand's static type is Float.
static inline Value prim_neg(Value a) { return VInt(-as_int(a)); }
// Widening coercions. `Char -> Int` is a no-op: a Char and its code point share the
// immediate encoding (`VChar('0')` is bit-identical to `VInt(48)`), so this compiles
// away. `Int -> Float` boxes (Float is a heap OBJ_FLOAT), so it does real work.
static inline Value prim_int_of_char(Value a) { return a; }
static inline Value prim_float_of_int(Value a) { return VFloat((double)as_int(a)); }
static inline Value prim_int_of_float(Value a) { return VInt((int64_t)as_float(a)); }
// `Int -> Char` (`Char.of_byte`): total, masks to the low byte. Char and Int share the
// immediate encoding, so this is just the masked int re-tagged as itself.
static inline Value prim_char_of_byte(Value a) { return VInt(as_int(a) & 0xFF); }
// Float arithmetic: unbox -> compute -> rebox. Codegen picks these (over the `prim_*`
// int forms) when the operands' static type is Float. Each result is a fresh heap box.
// `prim_fmod` is C `fmod` (IEEE remainder toward zero), matching the interpreter's `%`.
static inline Value prim_fadd(Value a, Value b) { return VFloat(as_float(a) + as_float(b)); }
static inline Value prim_fsub(Value a, Value b) { return VFloat(as_float(a) - as_float(b)); }
static inline Value prim_fmul(Value a, Value b) { return VFloat(as_float(a) * as_float(b)); }
static inline Value prim_fdiv(Value a, Value b) { return VFloat(as_float(a) / as_float(b)); }
static inline Value prim_fmod(Value a, Value b) { return VFloat(fmod(as_float(a), as_float(b))); }
static inline Value prim_flt(Value a, Value b) { return VBool(as_float(a) < as_float(b)); }
static inline Value prim_fgt(Value a, Value b) { return VBool(as_float(a) > as_float(b)); }
static inline Value prim_fle(Value a, Value b) { return VBool(as_float(a) <= as_float(b)); }
static inline Value prim_fge(Value a, Value b) { return VBool(as_float(a) >= as_float(b)); }
static inline Value prim_feq(Value a, Value b) { return VBool(as_float(a) == as_float(b)); }
static inline Value prim_fneg(Value a) { return VFloat(-as_float(a)); }
// `prim_show` is monomorphised: codegen picks the right leaf from the argument's
// static type. Only the primitive (leaf) types reach these -- compound values are
// rendered by their `Display` witnesses, which recurse through the leaves.
Value prim_show_int(Value x);
Value prim_show_float(Value x);
Value prim_show_char(Value x);
Value prim_show_text(Value x);
Value prim_print_endline(Value x);
// Concatenate `n` text values (used by string interpolation).
Value prim_str_concat(size_t n, ...);

// The heap constructors (`mk_closure`/`mk_tuple`) and the collector API live in
// gc.h, since they are what the garbage collector manages.

// Apply a closure value to an argument.
static inline Value apply(Value f, Value x) { return as_closure(f)->desc->code(f, x); }

// Apply a closure value to `n` arguments at once (the flattened spine of a
// nested application). When `f` is the head of a curried chain whose remaining
// arity is exactly `n` and it carries an uncurried `worker`, dispatch straight
// to the worker -- no intermediate currying-stage closures are allocated. Every
// other shape (no worker, partial application `n < arity`, over-application
// `n > arity`, or a plain single-stage closure) falls back to applying one
// argument at a time through `code`, exactly reproducing the curried semantics.
static inline Value apply_n(Value f, size_t n, Value *args) {
    const ClosureDesc *d = as_closure(f)->desc;
    if (d->worker && d->arity == n) {
        return d->worker(f, args);
    }
    Value r = f;
    for (size_t i = 0; i < n; i++) {
        r = apply(r, args[i]);
    }
    return r;
}

// i-th element of a tuple value (also used for record ordinals).
static inline Value proj(Value t, size_t i) { return as_tuple(t)->elems[i]; }

// A constructor value's i-th field. Codegen knows statically whether a value is
// a tuple or a constructor -- tuple/record access uses `proj`, constructor
// access uses this -- so no runtime kind check here. `data_tag` (which
// constructor) reads the header's `ctag` byte and so lives in gc.h.
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
extern Value builtin_not;
extern Value builtin_neg;
extern Value builtin_int_of_char;
extern Value builtin_float_of_int;
extern Value builtin_int_of_float;
extern Value builtin_char_of_byte;
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
