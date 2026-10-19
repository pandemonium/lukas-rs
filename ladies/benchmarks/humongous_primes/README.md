# Humongous-prime optimizer benchmark

This is the arithmetic kernel of the interactive prime finder, frozen as a
deterministic native-backend workload. It builds `M(521) = 2^521 - 1` with the
list-based `Big` implementation and runs all nine Miller-Rabin witnesses. Because
`M(521)` is prime, the test follows the full successful path rather than finding
an early composite witness.

Run it with wall-clock and GC measurements:

```sh
./ladies/benchmarks/run.sh humongous_primes
```

Add the allocation histogram when investigating a pass:

```sh
MARM_ALLOC_STATS=1 ./ladies/benchmarks/run.sh humongous_primes
```

The initial baseline measured on 2026-10-07 was 5.15 seconds and 33,662 MB
allocated. The allocation histogram reported about 1.03 billion arity-two data
objects (69.95%) and 442 million arity-two tuples (30.05%), with only 202
closures. The exact time is machine-dependent; allocation volume and output are
the more stable signals.

The first optimizer result was direct tuple matching: a tuple literal consumed by
`deconstruct` is held in separate C locals and a whole-value fallback reconstructs
it only on the selected branch. On the same machine that changed:

| Measurement | Before | After | Change |
| --- | ---: | ---: | ---: |
| Wall time | 5.15 s | 4.12 s | -20.0% |
| Allocation | 33,662 MB | 23,685 MB | -29.6% |
| Arity-two tuples | 442.0 million | 6.1 million | -98.6% |

The next large opportunity is visible in `make`, `halve`, arithmetic, and modular
arithmetic: they repeatedly build and consume immutable limb lists. Deforestation,
constructor sinking, or scalar replacement can remove `Cons` cells without
changing the source program. Arity-two data objects now account for 99.4% of
allocated bytes.

A generic direct-constructor pass now scalar-replaces known constructor fields of
any arity when a match consumes them locally. It understands constructor identity,
field count, patterns, and escape; it has no `List`/`Cons` special case. Whole-value
fallbacks materialise the constructor only in the selected branch. This removes
local constructor/match pairs left behind by the simplifier, including nested and
literal subpatterns, but M(521) remains at 23,685 MB and 1.029 billion arity-two
data objects. Its hot `Cons` cells are returned by one recursive worker and consumed
by another, so they cross the boundary of local scalar replacement. Merely widening
the local arity limit cannot affect this workload.

The next pass recognizes a recursive spine rebuild from typed control and data
flow and replaces it with an in-place pointer reversal. A qualifying worker
deconstructs a recursive sum with one terminal and one step constructor, returns
the seed at the terminal, invokes a reconstruction callback in the step, and
tail-recurses through the sole recursive field. The callback must reconstruct
that same constructor with the accumulator in the recursive field. No type,
constructor, module, or function name participates in recognition.

With the pass toggled on and off in the same compiler build, five alternating native
runs measured:

| Measurement | Without owned spines | With owned spines | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 3.88 s | 3.13 s | -19.3% |
| Allocation | 23,685.1 MB | 10,299.2 MB | -56.5% |
| Minor collections | 92 | 40 | -56.5% |
| Arity-two data objects | 1,028,751,647 | 443,914,042 | -56.8% |

`halve` is now written as a `List.fold_right` over the original little-endian
digits. This expresses the significant-to-insignificant carry flow directly and
removes the input reversal, while keeping `make` as the normalization boundary.
Five alternating runs against the previous tail-loop source measured:

| Measurement | Tail loop | `fold_right` | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 2.95 s | 3.02 s | +2.4% |
| Allocation | 10,299.2 MB | 10,403.4 MB | +1.0% |
| Arity-two data objects | 443,914,042 | 383,485,963 | -13.6% |
| Arity-two tuples | 6,065,146 | 71,042,966 | +1,071.2% |

The fold removes 60,428,079 `Cons` cells, but its pair state initially allocated
one tuple per digit plus one seed tuple per call: 64,977,820 new tuples.

The next pass adds a general owned-tuple calling convention. It does not identify
`fold_right`, `List`, or either constructor. A worker gets an owned-parameter
variant when dataflow proves that the parameter supplies every result path. A
fresh tuple selects that variant, recursive calls propagate the ownership, and a
higher-order closure can advertise an owned-last-argument worker. A step which
destructures its accumulator once and returns a tuple of the same arity computes
all replacement fields first, then updates the owned tuple with the generational
write barrier. The dynamic fallback computes an ordinary result and copies it
into the owned box, keeping the calling convention sound for unknown closures.

Five alternating native runs against an opt-out build of the same compiler
measured:

| Measurement | Without owned tuples | With owned tuples | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 3.27 s | 3.18 s | -2.8% |
| Allocation | 10,403.4 MB | 9,020.3 MB | -13.3% |
| Minor collections | 40 | 35 | -12.5% |
| Arity-two tuples | 71,042,966 | 10,614,887 | -85.1% |

The exact 60,428,079 removed tuples are the per-digit accumulator results. The
remaining 4,549,741 tuples above the old tail-loop count are the one-per-call
seeds.

The next extension carries a fresh tuple seed through an ownership-preserving
call as a virtual aggregate in the consuming match's C stack frame. It keeps the
ordinary `Value` calling convention, uses the existing owned-worker analysis,
and materialises a heap tuple only if the value escapes. This is independent of
`fold_right`, `List`, and the tuple's element types. Five alternating runs of one
compiler build measured:

| Measurement | Heap seed | Virtual seed | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 3.75 s | 3.74 s | -0.3% |
| Allocation | 9,020.3 MB | 8,916.1 MB | -1.2% |
| Minor collections | 35 | 34 | -2.9% |
| Arity-two tuples | 10,614,887 | 6,065,146 | -42.9% |

The exact 4,549,741 seed tuples disappear. A full unboxed small-product ABI can
also remove the in-place field writes, but the remaining allocation target is
now overwhelmingly the recursive constructor data below. At this size the wall
change is within run-to-run noise; the stable gains are the exact object count,
104.2 MB less allocation, and one fewer nursery collection.

After that, the remaining allocation is still almost entirely recursive arithmetic
data. Result spines from `add_digits` and `sub_digits` require broader recursive
producer/consumer fusion or a different representation.

Worker specialization and tail-call lowering are useful secondary targets. The
tiny closure count shows that existing lambda lifting already handles the local
recursive workers well.

For compiler A/B testing, `ladies/benchmarks/compare-head.sh` copies this exact
source into the archived `HEAD` tree, alternates the run order, verifies identical
standard output, and records median wall time and allocated megabytes. Keep the
workload source unchanged while measuring an optimizer pass so the comparison
remains meaningful.

The recursive-data extension recognizes a general recursive eliminator, also
called a catamorphism: a worker deconstructs one recursive input, returns a
product seed at the terminal constructor, recursively eliminates the sole
recursive field, and passes that result to a combiner. When ownership analysis
also proves that the product and input node are exclusive, the combiner can
reuse both. This definition is entirely structural. It contains no knowledge of
`List`, `fold_right`, constructor spellings, qualified names, or standard-library
identities; renamed custom `Chain` and `Spine` types exercise it in the codegen
regression tests.

Five alternating native runs of one compiler build, with
`MARM_NO_OWNED_DATA=1 MARM_NO_DYNAMIC_OWNERSHIP=1` for the control executable,
measured:

| Measurement | Without owned data | With owned data | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 3.86 s | 3.38 s | -12.4% |
| Allocation | 8,916.1 MB | 3,454.0 MB | -61.3% |
| Minor collections | 34 | 13 | -61.8% |
| Arity-two data objects | 383,485,210 | 144,843,891 | -62.2% |

Exactly 238,641,319 constructor allocations became in-place replacements. The
remaining cells are not all removable construction/deconstruction pairs: some
materialize live results while both arithmetic operands remain reachable, and
some begin an ownership cycle from a shared constant. Eliminating those requires
alias-group ownership across calls, destination-passing arithmetic, or a packed
limb representation rather than another local peephole.

Together, the structural spine rebuild and recursive-eliminator ownership paths
restore the earlier allocation result without identifying a library fold. A
same-build control disables both structural paths with
`MARM_NO_OWNED_SPINES=1 MARM_NO_RECURSIVE_ELIMINATOR_OWNERSHIP=1`. Three
uninstrumented control runs took 4.66, 4.72, and 4.68 seconds; five enabled runs
took 3.39, 3.39, 3.39, 3.38, and 3.39 seconds.

| Measurement | Structural paths disabled | Current compiler | Change |
| --- | ---: | ---: | ---: |
| Uninstrumented median | 4.68 s | 3.39 s | -27.6% |
| Allocation | 22,302.0 MB | 3,454.0 MB | -84.5% |
| Minor collections | 87 | 13 | -85.1% |
| Arity-two data objects | 968,323,557 | 144,843,891 | -85.0% |

Allocation-site attribution then showed that nearly all remaining constructor
traffic came from two ownership-provenance gaps rather than a missing arithmetic
primitive. First, a recursive destination used once in each arm of an `if` was
counted twice syntactically even though only one arm executes. Ownership is now
linear per control-flow path, allowing recursive producers to keep writing into
the same destination through either arm. Second, a fresh recursive value returned
inside a product lost its provenance when the product was represented as a virtual
stack aggregate and immediately destructured. Field-level provenance now crosses
that boundary when every result path constructs the field freshly.

These are general destination-passing rules. They use liveness, inferred types,
recursive constructor shape, and control flow; they do not identify the benchmark,
its arithmetic functions, `List`, or a fold declaration. A separate appended
destination parameter was unnecessary because the existing owned-data worker ABI
already carries a suitable recursive argument as its destination once provenance
survives to the call.

Five uninstrumented runs after this extension took 3.00, 3.10, 3.11, 3.09, and
3.10 seconds. Allocation statistics from the same build measured:

| Measurement | Before | After | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 3.39 s | 3.10 s | -8.6% |
| Allocation | 3,454.0 MB | 169.0 MB | -95.1% |
| Minor collections | 13 | 0 | -100% |
| Arity-two data objects | 144,843,891 | 1,318,772 | -99.1% |

The pass eliminates another 143,525,119 arity-two constructor allocations. The
remaining allocation is now dominated by 6,065,146 arity-two product objects;
recursive data accounts for 17.9% of allocated bytes rather than 96.0%.

Allocation-site attribution showed that those products were not recursive fold
results. Exactly 6,065,051 came from the terminal fallback in `Big.compare`.
Direct multi-scrutinee matching had already scalar-replaced `xs, ys` into two C
locals, but the `_` fallback was represented by a whole-tuple binder. Although
that binder was dead, code generation reconstructed the tuple before returning
the accumulated comparison result.

Direct product and constructor matching now applies clause-local liveness to its
pattern bindings. It materializes a scalar-replaced whole value only when the
clause body reads that binding; dead whole-value and nested field bindings emit
no object. The original scrutinee elements are still evaluated into locals before
matching, so their evaluation order is unchanged. This rule is based on pattern
dataflow and applies to products and arbitrary-arity constructors, without any
knowledge of `Big.compare` or its types.

Five interleaved same-compiler runs used `MARM_NO_DEAD_PATTERN_BINDS=1` for the
control executable and produced identical output:

| Measurement | Dead binds materialized | Dead binds removed | Change |
| --- | ---: | ---: | ---: |
| Median wall time | 2.37 s | 2.33 s | -1.7% |
| Allocation | 169.0 MB | 30.2 MB | -82.1% |
| Arity-two tuples | 6,065,146 | 95 | -100.0% |

The pass removes exactly 6,065,051 tuple allocations. The profile is now almost
entirely the remaining 1,318,772 arity-two recursive data objects; only 187 tuple
objects of all arities are allocated during the complete workload.

The wall-clock rows throughout this file are paired comparisons made at different
points during development. They establish the change within each row, but their
absolute times should not be read as one continuous series: machine load,
temperature, generated code, and GC instrumentation differed between sessions.

Native sampling after the allocation work showed that owned recursive rebuilds
still executed as ordinary C recursion. The generated worker mutated a node only
after its recursive call returned, leaving one C activation per limb even though
the input spine was exclusive.

Owned-data workers now use a forward mutation loop when structural analysis proves
that every rebuilding path places a saturated self-call in the constructor's final
recursive field and advances the owned parameter to the matched recursive binder.
Each iteration evaluates the replacement payload and next-call arguments before
mutating the current node. A terminal or unsupported suffix is evaluated by the
ordinary worker and attached through a write-barrier-aware field update. The rule
uses constructor shape, types, ownership, and dataflow; it contains no source-level
function, type, constructor, or module names.

Five alternating runs compared one compiler build with and without
`MARM_NO_OWNED_DATA_LOOPS=1`.

| Measurement | Recursive owned worker | Forward owned loop | Change |
| --- | ---: | ---: | ---: |
| Median user time | 2.45 s | 2.29 s | -6.5% |
| Arity-two data objects | 1,318,772 | 1,318,772 | unchanged |
| Owned data replacements | 321,738,359 | 321,738,359 | unchanged |

This optimization removes call and return traffic rather than allocations. The
generated owned variants for addition, subtraction, and digit multiplication no
longer call themselves, while the ordinary immutable workers remain available for
shared or terminal suffixes.

The suffix attachment skips an identity write when the ordinary suffix returns
the terminator already stored in the parent. This matters for parallel workloads:
without the check, the redundant write enrolled old nodes in the remembered set
and serialized `billions` on its GC lock. With the check, five alternating runs
measured 2.23 seconds median for the looped build and 2.26 seconds for the opt-out
build, with the same output and 29.5 MB allocation.
