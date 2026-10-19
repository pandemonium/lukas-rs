# Humongous prime finder

An interactive, native-backend example with arbitrary-size unsigned integers,
an arithmetic expression parser, and Miller-Rabin probable-prime testing. The
implementation is Marmelade; there is no example-specific C companion.

Build and run it from the repository root:

```sh
./compile-lady.sh --backend native ladies/interactive/humongous_primes
./ladies/interactive/humongous_primes/exe
```

The prompt accepts:

```text
check 2^127 - 1
next 10^100
find 200 digits
find between 10^80 and 10^80 + 10000
check M(127)
help
quit
```

The prompt has in-session history: Up/Down or Ctrl-P/Ctrl-N browse earlier
commands. Left/Right, Home/End, Delete, Backspace, Ctrl-A, Ctrl-E, and Ctrl-U edit
the current line.

Expressions contain non-negative decimal integers, parentheses, `+`, `-`, `*`,
and `^`, with normal precedence. Exponentiation is right-associative. `M(n)` is
shorthand for `2^n - 1`. Exponents and digit counts are deliberately limited to
less than one million; evaluated integers may be much larger.

`check` and successful searches report a *probable* prime. Each candidate passes
small-prime division and nine fixed Miller-Rabin witnesses. This is intended for
language and number-theory exploration, not cryptographic key generation. The
pure Marmelade arithmetic favors readable code over a dedicated big-integer library.
On the current native build, representative searches took about 0.2 seconds at
30--50 digits, 4.5 seconds at 100 digits, and 23 seconds at 200 digits. Exact
times vary with the distance to the next prime. Checking a supplied prime is
usually faster than searching for one.

## Optimizer workload

A deterministic native benchmark containing the same arithmetic kernel lives at
[`ladies/benchmarks/humongous_primes`](../../benchmarks/humongous_primes/). It
checks the Mersenne prime `M(521)` and keeps the code deliberately high level so
compiler changes can attack temporary match tuples, tail calls, constructor
wrappers, limb lists, and short-lived allocation.

The first pass added for this workload fuses tuple literals directly into pattern
matching. On `M(521)` it removed 98.6% of tuple objects, reduced total allocation
by 29.6%, and reduced wall time by 20.0% on the baseline machine. The benchmark
README records the measurements and the next optimization target.

Run one measured build with allocation and GC statistics:

```sh
./ladies/benchmarks/run.sh humongous_primes
```

The repository-wide A/B runner also discovers it automatically:

```sh
ROUNDS=3 ./ladies/benchmarks/compare-head.sh
```

That runner compiles the exact same benchmark source with the working compiler and
`HEAD`, alternates run order, checks byte-identical output, and reports median wall
time and allocated megabytes in `build/benchmark-head/summary.tsv`.
