# Five-g opposite-core factor probe: explicit carries and width

Status: 2026-11-04. **Completed structural prototype and independent
semantic tests.** This is NOT yet a fast weighted five-round carryDP.

## Goal

The five-round opposite core for the proved seven-round boundary
reduction uses the true fixed-key Feistel difference:

    (0,a) -> (b,0).

Let r=x2 and z=x3. For genuine base words,

    x1 = z XOR g(k1,r)
    x4 = r XOR g(k2,z)
    x5 = z XOR g(k3,x4).

Let p,q,t be the intermediate right-half differences. Five *real*
derivative conditions are

    Delta g(k0,a,x1) = p
    Delta g(k1,p,r)  = a XOR q
    Delta g(k2,q,z)  = p XOR t
    Delta g(k3,t,x4) = q XOR b
    Delta g(k4,b,x5) = t.

The prototype in `opposite_five_tagged.py` unfolds every g into eight
RFC 8891 S-box digit steps. Each step propagates the two genuine
addition carry bits. The emitted base tags U and derivative tags E
are rotated left by 11, *then* the five derivative and three base
relations are imposed simultaneously.

The construction has no factorized marginal-DDT approximation and no
path-independence assumption. It defines the exact real 32-bit fiber.

**Important limitation:** its counting backend is still Z3 model
enumeration with terminal UNSAT, not an independent weighted
HashMap/carry transfer. The local tag encoding is independent of the
existing direct and middle-word SMT circuits, but they are all SMT
backends. Count claims are computationally verified, not Lean-proved.

## Exact semantic regression

`python3 Magma/Differential/FiveRounds/Experiments/five_factor_gate.py`

| Fixed 5-core keys k0..k4 | Input (0,a), output (b,0) | Complete local tags | Independent middle SMT |
|---|---|---:|---:|
| [0, 0x2056, 0xfdfa7789, 0xf0f8d960, 0] | a=0x80000000, b=0x681e60a7 | 2 | 2 |
| same | a=0x00000001, b=0x00000001 | 0 | 0 |
| same | a=0x80000000, b=0x681e60a6 | 0 | 0 |
| [0x12345678, 0x2056, 0xfdfa7789, 0xf0f8d960, 0x87654321] | a=0x80000000, b=0x1d43093d | 8 | 8 |

Every completed enumeration reaches UNSAT and independently replays
each base pair through the full five-round Feistel function. The
two independently enumerated sorted middle-pair sets have identical
SHA-256 hashes for all four cases. The last case tests that the
local tag semantics are NOT accidentally specialized to zero outer
keys.

For any UNKNOWN or model cap, output is only a lower bound; zero is
never inferred.

## Structural variable elimination probe

`five_factor_width.py` builds a coarse nibble-level primal factor
graph: five genuine carry/S-box constraints, five derivative
relations, and all three base-word relations.

`five_factor_bit_width.py` refines emitted tags to individual bits
because rotate-left-11 splices **3 bits from one nibble and 1 bit from
its neighbor**. In the default a=0x80000000,k0=0 case, only the top
input nibble contributes to the first g derivative. Therefore its
emitted nonzero tag can occupy only S-box position 7 and the first
intermediate difference p can occupy only output bits 7..10. These
are exact simplifications for this specified case, not for arbitrary
keys or differences.

| Graph | Nodes | Factors | Greedy min-fill maximum factor scope |
|---|---:|---:|---:|
| Whole-nibble tags, no semantic simplification | 163 | 104 | 212 bits |
| Bitwise rotated tags, top-nibble first-g simplification | 307 | 233 | 103 bits |

The figures refer to a **heuristic dense-table scope
overapproximation**, not a measured frontier size, a memory allocation,
a runtime, or a treewidth lower bound. A dense table with 103 free
bits is wholly impractical; exact sparse/constraint-aware elimination
could be vastly smaller. This result rules out blindly expanding
the existing triple-g dense/HashMap state interface, but does NOT
rule out a feasible exact five-g transfer.

The factor planner is *structural*: it does not exploit numeric
S-box sparsity. Its width numbers are useful for choosing a new
elimination strategy, but are NOT actual DDT coefficients.

## Genuine integer-weight sparse factor join (experimental)

`five_factor_sparse.py` is a second, independent counting backend.
It explicitly builds 0/1 finite-domain tables for each genuine
nibble-local g/carry step, each bit-rotated derivative identity and
all three real base equations. Variable elimination multiplies
factors and **sums exact Python integer weights** on projection.
It uses NO Z3 and does not enumerate all 32-bit base pairs.

    python3 Magma/Differential/FiveRounds/Experiments/five_factor_sparse_regression.py

Ten deterministic **4-bit one-S-box five-round Feistel toy** tests
finished with exact equality to independently exhaustive direct
Feistel DDTs, including positive counts 4 and 2, zero cases, and
the full zero-difference mass 256. They validate the weighted
semiring implementation, not full-width RFC complexity.

| Exact sparse join experiment | Limit | Excluded variables | Observed peak rows | Status |
|---|---:|---:|---:|---|
| 4-bit toy | 300,000 rows | 40 / 40 | 32,768 | COMPLETE, matches direct enumeration |
| 8-bit two-nibble toy | 600,000 rows | 42 / 85 | 262,144 | LIMIT, not a DDT |
| Full RFC 32-bit positive, sparse | 30,000 rows | 103 / 307 | 16,384 | LIMIT, not a DDT |
| Full RFC 32-bit positive, sparse | 250,000 rows | 171 / 307 | 131,072 | LIMIT, not a DDT |
| Full RFC 32-bit positive, sparse | 1,000,000 rows | 173 / 307 | 262,144 | LIMIT, not a DDT |

The full-width row counts are observed intermediate *factor-table*
rows, not the number of accepted complete automaton states.
The stop limit also applies while constructing a join; the largest
completed table can therefore be smaller than the configured cap.
Alternative scope-first and naive sparse-density orders were tested
at 250,000 rows and did not improve the full-width elimination.

The prototype is intentionally bounded and returns `LIMIT` without a
`weighted_count` field when it cannot finish. It supports arbitrary
fixed keys and differences in the complete five-chain formulation;
only a=0x80000000,k0=0 activates the proved first-g top-nibble
shortcut. It also supports non-RFC one-/two-nibble toys solely for
testing the exact integer-weight algebra.

## Remaining gate: compression rather than more memory

A **fast full-width weighted five-chain counter is still OPEN**.
A straightforward sparse relational join is not sufficient for
our 2,0,0 and 8 control cases at practical limits. The next
algorithmic step must use a much stronger representation: grouped
bit constraints with support propagation, conditional elimination
or a compressed symbolic/decision-diagram frontier. A successful
candidate must complete all four fixed-key RFC controls using its
OWN weighted counting backend and independently match the #SMT
oracles. Report COMPLETE/LIMIT, time, table/frontier size and exact
integer masses; do not infer a zero from a limit.

The verified seven-round fixed-key counts still come from SMT,
not from a scalable five-chain carryDP. Do not substitute a
three-round support relaxation for exact counting. Keep the
formal Rust-weights, premature Rayon optimization, and bulk
nine-round search freezes in force.
