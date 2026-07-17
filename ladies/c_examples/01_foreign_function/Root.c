// C implementation of the `foreign` declarations in Root.lady.
//
// Each is written with FOREIGN_DECL (from runtime.h, pulled in via gc.h). The
// macro name is the Marmelade name mangled to `<Module>_<member>` -- the same
// name the compiler emits at the call site. The body operates on ordinary C
// values; the macro handles marshalling to and from the boxed `Value`, builds
// the curried closure, and defines the global the compiler initialises.
#include "gc.h"

// isqrt : Int -> Int  (arity 1)
FOREIGN_DECL(int64_t, Root_isqrt, int64_t, n, {
    int64_t r = 0;
    while ((r + 1) * (r + 1) <= n) {
        r++;
    }
    return r;
})

// pow : Int -> Int -> Int  (arity 2; first argument captured, second applied)
FOREIGN_DECL(int64_t, Root_pow, int64_t, base, int64_t, exp, {
    int64_t acc = 1;
    while (exp-- > 0) {
        acc *= base;
    }
    return acc;
})
