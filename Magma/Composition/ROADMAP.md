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

## Full RFC structural composition: 2026-11-04 milestone

The native round-key schedule is H|H|H|reverse(H), where H is the
same eight-round Feistel block. Because the RFC final round is
GStar (no final swap), the actual cipher C obeys
C = H^-1 o J o H^3 and H o C o H^-1 = J o H^2.
This is proved against native roundKey and encrypt in
Magma/Diffan/FullScheduleConjugacy.lean. Its exact DDT
reduction is only in the H-pulled-back difference geometry,
NOT in ordinary XOR. The cipher-independent n-fold generalization
is in Diffan/ReflectedMacroSchedule.lean.
See [FULL_SCHEDULE_REFLECTION.md](FULL_SCHEDULE_REFLECTION.md).

**F4 — exact carry/frontier local-variable exclusion: FROZEN NOW.**
Do not pursue faster 32-bit join/ADD/BDD or a new SAT batch merely
because the tool exists. The primary research target is new
compositional laws and conditions for retaining or discarding
state labels. Targeted SAT checks up to 600 seconds remain allowed
when they settle a concrete mathematical uncertainty.

## 2026-11-04: the first surviving untransformed XOR invariant

See [TRANSPORTED_XOR_INVARIANT_AUDIT.md](TRANSPORTED_XOR_INVARIANT_AUDIT.md).

The 16-round palindromic REAL Magma block E16, with same
eight 32-bit key words forward and reverse, obeys the exact
ordinary-XOR integer-DDT duality
  D_E16(alpha,beta) = D_E16(J beta,J alpha).
The same reflected duality holds for the ordinary LAT
and, more generally, ALL integer two-observable correlations.
No transported difference convention and no 2^64-base cache.
Proved in Magma/Diffan/FullScheduleXorSymmetries.lean; an
independent 4-bit-word toy checked ALL 65,536 DDT cells and
ALL 65,536 LAT cells, and
a full-width real-RFC mirror witness was replayed.

The full 32-round C32 is key-dependently H-conjugate to
L=J H²; its permutation cycle-count power traces
are conserved for ALL powers (generic Lean theorem
Diffan/ConjugacyCycleInvariants.lean). Ordinary fixed
Walsh-mask correlations need NOT match (toy -4 vs +12).

The proposed low-tet layer of tau_H does NOT satisfy
a sufficient-quotient criterion: two genuine RFC
8-round states with identical low nibbles of BOTH
halves have different projected tau for high-only
alpha=8000000000000000. Diffan/TransportedXorQuotients.lean
formalizes the exact iff quotient stability criterion
and the XOR-coset obstruction when all differences
must descend. It also proves a generic 2-element
orbit invariant, far too weak for full-width exact DDT.

No base-free small quotient for the actual full-32
ordinary-XOR DDT has yet been established. F4 remains
FROZEN; next goal is algebraic labelled-transducer
congruence, not another long SAT or carry-join run.

## Full-32 original-XOR key gauge: DDT, LAT and BCT

**2026-11-04 follow-up: [FULL_KEY_MSB_GAUGE.md](FULL_KEY_MSB_GAUGE.md)**

For every 256-bit master key K let K' be K XOR the
256-bit mask 0x80000000 repeated in EACH of its
eight 32-bit words, and t=0x8000000080000000
be a 64-bit state-word XOR mask.

For ACTUAL RFC encryption, all 32 rounds including
the last no-swap GStar,

    E_K'(x XOR t) = E_K(x) XOR t.

This is proved for ALL keys and input states in
Magma/Diffan/FullKeyMSBGauge.lean using the exact
modular arithmetic/S-box/ROL11 identity
g_(k XOR 2^31)(x XOR 2^31)=g_k(x).

The difference geometry is the ORIGINAL XOR, so

    D_E_K'^XOR(a,b) = D_E_K^XOR(a,b)

for ALL full 64-bit a,b, with EXACT natural-number
multiplicities, not just support. Master-key flip
orbits have size exactly TWO. This only exhibits a
two-key equivalence under one action, not a full
classification of key-equivalence classes.

A new GENERIC exact inverse-sensitive
boomerang-connectivity table transport theorem in
Diffan/BoomerangGauge.lean (for any DifferenceSpace)
gives the full native RFC BCT counterpart

    BCT_E_K'(a,b) = BCT_E_K(a,b).

The full signed LAT transforms by a known sign
depending on the four top input/output mask bits;
its absolute values are equal. The generic proof
transports arbitrary Int observables and their
translation eigenvalues, without independence.

One-Sbox 4-bit-word toy: independently verified
ALL 65,536 entries of the FULL 32-round DDT,
ALL 65,536 signed LAT entries and ALL 65,536 BCT
entries across the paired keys. Full 32-bit RFC
pointwise control includes 1024 plaintexts and
256 independently computed inverse ciphertexts.
No full-width DDT/BCT is actually enumerated.

This is a key-dependent *affine* isometry invariant,
NOT a within-one-key compact XOR-DDT quotient.
It is general to other Feistel schedules with
the same round-function top-bit gauge and does not
constitute a full-Magma cryptanalytic break.
Carry/BDD/SAT optimization F4 remains FROZEN.

## 2026-11-05: attack-observability gate (no fake full-key break)

**Read [FULL_32_ATTACK_GATE.md](FULL_32_ATTACK_GATE.md) first.**
For the TRUE 16-round palindrome [0..7,7..0], Lean now proves
EXACTLY 2^32 publicly detectable matches E16(x)=J(x)
for all keys. This yields a genuine unknown-key 16-round
oracle distinguisher using ~2^32 chosen inputs, against
an ideal-permutation single-input probability 2^-64.

For the full native C32=Q16 o H², the same test does
NOT directly survive: the needed H²(x) is unknown.
Across 600 random 8-bit-total-state toy keys, the full
cipher has ~1 fixed/swap match, not 16. A real RFC test
refutes ALL 12,285 nontrivial reduced public operator
identities of length <=12 on {C,C^-1,J}. An exact
small-group image test finds all even cycle TYPES
represented in an abstract 8-state full-macro model.
Neither test is a full-width security proof.

A FULL 32-round TWO-query RELATED-KEY distinguisher does
exist (real RFC K and K xor highest bit of each word),
with ideal independent-key false positive 2^-64;
Lean now specifies its actual oracle interface.
Diffan/OracleObservableBarrier.lean proves that such a
related-key gauge alone cannot restrict ANY individual
single-key permutation: every arbitrary permutation
admits a formal conjugate partner.

**Standard one-unknown-key 32-round distinguisher/key
recovery remains OPEN.** New research must start with
a public test, a random-permutation baseline, and a
concrete data/time estimate before building a solver.
F4 sparse carry/BDD/SAT optimization stays FROZEN.

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

## 2026-11-04: exact nine-round reflected four-G crossing is Lean-certified

**LATEST P0 DESIGN FREEZE: [COMPOSITIONALITY_DESIGN_FREEZE.md](COMPOSITIONALITY_DESIGN_FREEZE.md).**
The reusable target is the BASE-LABELLED conditional four-round kernel
T_H, composed with its half-swapped image in an exact self-Gram;
see Diffan/ConjugatedDifferenceSpace.lean,
Diffan/TwistedConditionalGram.lean and the Lean theorem
nine_ddt_eq_twisted_four_round_gram.
The local pair-carry semiring engine is independently exact for
all 225 4-bit opposite boundary cells, but its 8-bit case LIMITs.
A materialized conditional-H cache reused one 4-round kernel
for all 225 toy endpoint queries: ~0.019s cache+joins versus
~0.354s independent 9-round brute, ~18.8x in one run.
An 8-bit toy four-query subset gave ~0.93s vs ~2.06s.
This is a verified MULTI-QUERY benefit but absolutely NOT
scalable to real 2^64-base-state Magma without compression.
The 32-bit scopes demand new bounded-frontier compression.
No new nine-round all-key impossible differential is claimed.

**New rigorous P0 result.** The true RFC 20..28 ordinary Feistel key
schedule `[4,5,6,7,7,6,5,4,3]` permits a reflection
`Q = J o H_rev o H = H^{-1} o J o H` where H consists of the first
FOUR rounds. `Magma/Diffan/NineReflection.lean` proves
`Q_involutive`, the exact integer DDT identity
`D9((a,0),(0,b))=D_Q((a,0),(0,b))`, D_Q symmetry, and exactly
2^32 fixed points for ALL selected key words.

**Most relevant new interface:**
`nine_ddt_eq_fourCrossingMass` proves by an explicit state-pair
BIJECTION that the original nine-round integer DDT equals the count
of `(x,y)` with BOTH `H(y)=J H(x)` and
`H(y xor (0,b))=J H(x xor (a,0))`.
The first equation uniquely fixes the correlated partner y.
There is NO product of independent four-round DDT coefficients.
The main nine-round theorem, fixed-point cardinality and symmetric
DDT have ZERO native `bv_decide` axiom dependencies according to
`#print axioms` (only the standard Lean propext, choice, quotient
axioms as applicable). See
[NINE_REFLECTION_CERTIFIED.md](NINE_REFLECTION_CERTIFIED.md).

A real-S-box first-active-digit support rule was independently checked
with fully symbolic RFC 32-bit key, base, and difference. Its complete
192-cell 7/8/9 outer nibble-class grid still excludes ONLY the six
existing seven-round classes. Thus single-round first-S-box-digit
support cannot by itself extend the universal zero to nine rounds.

Bounded Z3: the two-four-G crossing and direct nine match exact
toy counts `2,0,2` for 4-bit words. An 8-bit toy returns
crossing `complete zero` in 2.0s vs direct 9 `UNKNOWN` at 5s.
For full 32-bit actual RFC Magma, BOTH tested methods returned
`UNKNOWN` at 6s. This is NOT a 32-bit nine-round zero or a
fast exact full-width counter. The next P0 is compressed,
carry-tag-aware H-crossing elimination preserving shared real base
words, measured on a full-width exact fixed-key control.

Bulk nine-round SAT, speculative parallel optimization and the
unrelated Rust aggregation proof remain FROZEN.

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
