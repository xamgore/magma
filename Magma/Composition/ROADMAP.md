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

## Phase 2 (P0/P1) — composable correlated block interface

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

**Next action:** formulate and test the inverse-oriented
five-round core (0,a)->(b,0), then turn it into an exact
seven-round outer count using the existing boundary theorem.
This is the shortest mathematically valid route from our
new five-round tool to additional rounds.
