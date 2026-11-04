# Roadmap: from exact five-round carryDP to 7/9+ rounds

Status: 2026-11-03. Research plan; no nine-round impossible
differential is claimed.

**Goal:** reusable, correlated and exact fixed-key RFC 8891 Magma
fiber composition, leading to new key-universal impossibility
criteria at 9+ rounds or a well-understood computational barrier.

## Starting point (completed)

- **joint_middle_transfer.rs** computes exact *full* fixed-key
  five-round outer DDT for (a,0) -> (0,b), by eliminating the
  entire 32-bit middle base h *inside* an eight-nibble
  carry/S-box-tag weighted transfer, without independence guesses.
- Full counts 768 and 30,720 were independently exhausted by Z3,
  reconstructing and replaying each real five-round Feistel base;
  an additional nontrivial zero case was checked.
- **JointTaggedAcceptance.lean** proves general equivalence
  of accepted local tags with the three real g derivatives.
  The weighted Rust aggregation itself is NOT kernel-proved.
- A zero for ONE fixed key is not a key-universal impossible
  differential. A nine-round impossible differential is NOT
  presently established.

## Explicit design freezes

**F1 — formal verification of the Rust weight aggregator: FROZEN.**
No further Lean proof of HashMap summation, cyclic-seed counting or
bulk one-off SAT witnesses merely for completeness. Keep
existing Lean semantic lemmas and successful lake build.
Unfreeze only if a subtle identity is required by a new
reduction, independent verification finds a discrepancy,
or a general theorem is essential for an actual all-keys
impossibility result. Experimental sorry/axiom declarations
may be documented in clearly opt-in modules, but never
presented as certified theorems.

**F2 — broad Rust optimization: FROZEN.**
No premature Rayon, SIMD or wholesale data-structure rewrites.
The 2^22 cyclic seeds are naturally parallelizable later;
preserve exact integer counts and reliable resource limits.
Optimize only after profiling the next multi-round algorithm.

**F3 — bulk nine-round SAT/motif hunts: STILL FROZEN.**
See ../NinePlus/DESIGN_FREEZE.md. Targeted Z3/#SAT for
independent verification of new DP results is allowed.

## Phase 0 — validate general fixed-key five-round baseline

Run the generic --keys/--alpha/--beta API against a curated,
diverse fixture set: zeros, positives, independent real
key schedules and strict correlation-defect examples.
Record DP count, frontier, edges, memory, wall time and
independent #SMT completion status. Replay all witnesses.
UNKNOWN/LIMIT is NEVER reclassified as a zero.
Retain small deterministic CI fixtures.

**Gate:** all completed cases agree; reproducible outputs.

## Phase 1 (P0) — unlock the *correct* seven-round core orientation

**Completed computationally (2026-11-03):** the exact inverse-oriented
five-round fiber is parameterized by two middle 32-bit base words;
two independent five-round SMT encodings and a full, independently
replayed seven-round Feistel SMT produced identical completed counts:
**2** for a nontrivial positive, **0** for a one-hot zero, and
**0** for a strict base-correlation zero. See
[SEVEN_CORE.md](SEVEN_CORE.md) and executable
`seven_core_regression.py`. The NEXT algorithmic improvement is a
fast weighted five-core transfer, not another fixed-key SAT witness.

The existing kernel theorem gives exactly:

    D7[(a,0) -> (0,b)] = D5_inner[(0,a) -> (b,0)].

Our current five-round Rust engine ONLY handles the
other orientation, (a,0) -> (0,b). Substituting it here
would be incorrect. The previously proved key-free
path reversal is NOT a fixed-key DDT reversal theorem.

Build a true five-round exact-fiber formula for
(0,a) -> (b,0), or generalize the transfer to full
two-half endpoints. Preserve the complete base/difference
couplings. Independently compare against actual full
five-round Feistel Z3 encoding, including positive and
zero cases, before applying the proved 7->5 boundary cut.

**Gate:** one or more complete, independently checked
nontrivial seven-round fixed-key counts. No guessed
orientation equivalences.

## 2026-11-04: NEW key-universal seven-round theorem and valuation classes

The first genuinely KEY-UNIVERSAL seven-round obstruction has
been established for real 32-bit RFC Magma:
for ANY seven independent round keys, if a and b are nonzero
and supported entirely in the highest input nibble, then

    D7_K((a,0),(0,b)) = 0.

This gives 225 impossible nontrivial endpoint pairs.
Magma/Diffan/SevenTopNibbleImpossible.lean proves the
five-chain contradiction and the exact D7=0 theorem
using both real Feistel base trajectories; Magma.lean
imports the file. No sorry/admit. Its #print axioms
audit reports **40 local native bv_decide proof-reflection
axioms** plus standard Lean axioms; it is NOT pure
kernel-only and the exact trust assumption is documented.

**Stronger symbolic mask result:** a key-independent
first-active-nibble (2-adic) valuation invariant of
g detects SIX disjoint seven-round endpoint families,
containing **1,908,225 distinct nonzero (a,b) pairs**.
The full symbolic Z3 checks use arbitrary keys/bases
for the local lemma, then arbitrary 32-bit endpoint words
with higher nibbles FREE for all 64 valuation classes.
See [NIBBLE_VALUATION_FAMILIES.md](NIBBLE_VALUATION_FAMILIES.md)
and nibble_universal_family_scan.py. The additional
1,908,000 pairs are NOW included in the parameterized
Lean theorem `seven_round_zero_six_nibble_classes`
(see Magma/Diffan/SevenNibbleValuationClasses.lean).
This preserves exact Feistel base-state correlations and
holds for every independent seven-key schedule.
The #print axioms audit reports 18 native
bv_decide proof-reflection axioms for the full theorem;
it is not a bare-kernel-only formal certificate.
The arithmetic identity 1,908,225 also has its own Lean
proof. No direct nine-round key-universal claim follows.

The weak valuation abstraction is SAT on the selected
eight- and nine-round targets, explaining why the
new seven-round proof does not automatically extend.
The next research gate is to lift richer S-box/carry
support constraints, or key-linked reflection, through
nine rounds without admitting independent marginal
DDT products. This targeted theorem research is
distinct from the frozen broad SAT/motif sweeps.

## Phase 2 (P0/P1) — composable correlated block interface

**New exact building block (2026-11-03):** the Rust joint
three-g carry transfer now accepts arbitrary 64-bit differences
`(aL,aR)->(bL,bR)`, instead of only `(0,a)->(b,0)`.
The full 32-bit RFC Magma count **48** for a nontrivial
four-active-half endpoint and a strict correlated **0** were
independently exhausted by Z3. The latter detects an obstruction
that survives all five independent local DDTs. The same
generalized executable passed all 15 legacy exact five-round
regressions, including 768 and 30,720. See SEVEN_CORE.md.

**Remaining P0:** implement an EFFICIENT correlated five-core join;
no all-32-bit non-SMT exact five-core counter is finished yet.
The central three-round support + outer local supports is a sound
necessary filter, NOT an exact five-core count.

**2026-11-04 two-J overlap research:**
[OVERLAPPING_J.md](OVERLAPPING_J.md) derives an exact 5=3+3-1
counting identity from two conditional three-round J predicates
sharing the COMPLETE base and XOR-difference state of their
common round. Independent full Magma #SMT verifies 2,0,0,8
with identical pair-set hashes. Scalar J DDT multiplication is
NOT valid: on a one-nibble toy it falsely admits all 136 exact
zero endpoints. A 24-bit interface ROBDD counts all 225 toy
DDTs exactly, but construction from unexpanded Boolean circuits
hits LIMIT already at 8-bit word size with naive variable orders.
The active challenge is compact nibble-local symbolic or weighted
carry/tag composition, NOT another brute-force fixed-key witness.

**2026-11-04 factor-probe gate completed (NOT full-width weighted DP):**
[FIVE_FACTOR_PROBE.md](FIVE_FACTOR_PROBE.md) provides an independently
replayed five-chain dual-carry/tag #SMT model (exact fibers 2,0,0,8)
and a local factor-graph width analysis. Even after splitting emitted
tags into bits and exploiting the top-nibble first derivative, a
simple greedy min-fill has a peak *dense scope* estimate of 103 bits.
This is NOT an observed frontier or lower bound. A first *exact
integer-weight* sparse factor contraction now exists in
`five_factor_sparse.py`: 10 one-nibble five-round toy DDTs match
independent exhaustive Feistel counting, but the real 32-bit
case reaches resource LIMIT after 173/307 variables with a
one-million-row cap. Stronger compressed elimination is OPEN;
see the measurements and stop rules in FIVE_FACTOR_PROBE.md.

Construct an exact weighted two-block join across a
full intermediate (base state, XOR difference) point.
Use existing five-round middle-fiber mathematics to
establish the correct reference expression; do NOT
multiply marginal DDTs or drop base-state correlations.

Experiment with a 7 = 3 + 1 + 3 inner-round decomposition
and alternate elimination orders. Compress the cut-point
labels only if the representation passes strict known
false-join regression and independent #SMT counts.

**Gate:** reusable multi-round transition that computes
or soundly prunes at least one case beyond the five-round
outer family, with measured runtime, frontier and errors.

## Phase 3 — investigate nine-round obstacles, not more witnesses

The exact boundary theorem reduces nine-round outer
(a,0)->(0,b) to SEVEN inner rounds (0,a)->(b,0).
For RFC window rounds 20..28, the seven inner key indices
are [5,6,7,7,6,5,4]; repeated keys must remain shared.

Compare base-correlated linked-key and independent-key
models *under otherwise identical constraints*. Measure
actual additional rejected transitions and reusable
constraints, not solver-time differences. Limit initial
cases to predeclared sparse candidates and verified controls.

A universal impossible differential requires proving
zero for ALL admissible 256-bit master keys under the
true RFC schedule. A single positive real witness
refutes a universal impossible-differential claim.
A fixed-key zero is insufficient. An unknown SAT run
is insufficient. Support-filter rejection is not
automatically a full endpoint impossibility result.

**Gate:** strict reusable pruning beyond existing filters
or a certified all-keys impossible differential. Otherwise
refreeze the case family rather than accumulate inconclusive
queries.

## Phase 4 — optimize the actual bottleneck, only then

Baseline full five-round DP: about 4.10 billion edges,
43,008 peak states and 35.9 seconds for the first fixture;
0.679 billion edges, 10,240 states and 6.65 seconds for
the second. Independent Z3 was 0.69 and 44.95 seconds
respectively: no universal performance advantage.

Possible improvements in measured order:
- Rayon over independent cyclic seeds with exact reductions.
- Early infeasibility cuts and precomputed local tables.
- Packed/sorted frontier structures where HashMap overhead
  dominates; lower-memory variable elimination orders.
- Compare against identical Z3/#SMT constraints and record
  performance and exact counts on all regression cases.

**Gate:** statistically meaningful speed/memory improvement
without a correctness regression.

## Claim discipline and immediate next action

Keep separate: Lean-proved statements; independently
exhausted computational counts; conditional assumptions;
heuristic support filters; timeouts and UNKNOWN.
The science target is new reusable exact elimination or
all-keys impossibility criteria, not additional huge
certificate files.

**Next action (two complementary P0 routes):**
(A) a nibble-local compressed interface for the two state-lifted J3
kernels in OVERLAPPING_J.md, tested on full 32-bit exact counts 2,0,0,8;
(B) the RFC window 20..28 reflection factorization in
[REFLECTION_J_OPTIONS.md](REFLECTION_J_OPTIONS.md):
Q = J o G_rev o G = G^(-1) o J o G, with G the first FOUR
rounds and [4,5,6,7,7,6,5,4] an eight-round key palindrome.
For this window, D9((a,0),(0,b))=D_Q((a,0),(0,b)) exactly.
This is a new *computational interface direction*, NOT a new
nine-round all-key impossibility theorem. Compare local carry/tag
contraction with external exact #SAT/#model-counting backends
(Ganak/d4/DPMC/ADDMC) before optimizing Rust or unfreezing SAT.
Keep shared real base states, correct key indexing, and explicit
COMPLETE/LIMIT semantics throughout.
