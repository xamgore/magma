# Bottom-up fiber composition: what is proved, what is missing

Status: 2026-11-03. Scope: **research roadmap, not a new theorem**.

The three supplied full-text papers are distilled in
[LITERATURE.md](LITERATURE.md): Liu et al. on carry-dependent tables,
Qin–Wu on adjacent-addition non-independence and #SAT, and
Kwon–Song on multistage characteristic graphs. These establish
precedents for our COMPONENT METHODS, not exact fixed-key Magma
DDT composition.
The nine-round SAT/parity motif branch is design-frozen in
`Magma/NinePlus/DESIGN_FREEZE.md`.

## Existing certified foundation — do NOT re-prove

1. `Magma/Diffan/FirstRoundDeletion.lean`:
   `twoSided_boundary_ddt_eq_inner` removes the two outer zero-half
   rounds **exactly**, at fixed round keys and with DDT multiplicity.

2. `Magma/Diffan/CorrelatedFiveMacro.lean`:
   `Correlated`, `Correlated.split`, `Correlated.reify` describe
   genuine base-and-difference traces and splitting at arbitrary
   round boundaries. Caveat: `Correlated` existentially quantifies
   independent per-round keys; `split` alone does **not** establish
   a fixed RFC master-key counting identity.

3. `Magma/Diffan/FiveRoundMiddleFiberMass.lean`:
   `fiveMiddleSigmaEquiv`,
   `five_count_eq_conditional_mass`, and
   `five_count_by_observation` provide **exact weighted joins over
   the FULL middle point** (base state AND difference), for one
   fixed RFC master key. Thus the essential five-round composition
   and exact cardinality logic are already proved.

4. `Magma/Diffan/FiveRoundBaseDeltaLabelAudit.lean`,
   `FiveRoundLabelJoinDefect.lean` and
   `FiveRoundGraphSyndrome.lean`: projecting the middle point
   down to only a base label or difference label can create
   false joins. These are *certified counterexamples* to naive
   marginal-DDT multiplication. Any compression must carry a
   correctness theorem, not an independence guess.

5. `Magma/Diffan/GCarryHalfSplit.lean`,
   `GCarryFiberTensor.lean`, `GFiberNibbleCorrelation.lean`:
   the one-round genuine g derivative has an exact 4-state carry
   boundary across two 16-bit blocks; there is a proved pointwise
   tensor/correlation decomposition.

6. `Magma/Diffan/ThreeCarryTraceJoin.lean`:
   `fiveRound_eq_three_carry_traces` expresses the REAL
   five-round outer DDT as an exact sum of three correlated
   carry-trace predicates. **The sum is still over full
   32-bit variables `r,h`; it is not a fast DP.**

7. `Magma/Diffan/GBaseTaggedCarryStep.lean` and now
   **`Magma/Composition/TaggedCarryWord.lean`**:
   the two S-box outputs share the SAME genuine incoming carry pair.
   `taggedPrefix_correct` proves all eight steps chain correctly;
   `taggedPrefix_eight_g` proves both real 32-bit outputs
   (base `g` and the XOR derivative) after rotate-left-11.
   **Whole-word reconstruction DONE; a full-width exact
   triple-fiber transfer matrix is still missing.**

8. `Magma/NinePlus/ParityCollision.lean` and
   `parity_transducer.py`: key parity is a sound reusable path
   filter for repeated master-key words when input g-difference
   is `1`. It rejects specific internal paths, not all paths
   for any new nine-round endpoint.

## Priority P0 — localize the existing *exact* triple correlation

This is the largest theory-to-algorithm gap, and should be tackled
before any fresh 9+ witness campaign.

`ThreeCarryTraceJoin.lean` explicitly notes that its inverse-middle
trace is represented by a forward carry trace at the **global**
preimage `middlePreimage key h`. That is semantically exact, but
it prevents nibble-local variable elimination in the `h`
coordinates. In addition, `g`'s 11-bit rotation couples nibble
boundaries, and the third derivative uses the XOR-related
base `r XOR h`.

**Milestone:** derive an executable exact local transition whose
state carries all indispensable constraints:
- the two addition carries of each participating g derivative;
- enough base S-box output digits to reconstruct the inverse-middle
  relation;
- the boundary bits created by rotate-left-11 and the third
  derivative's XOR coupling;
- a fixed key nibble (and shared key identity where the schedule
  repeats).

Prove its accepted weighted paths equal the already certified
`threeTraceCondition` count, first on one nibble and then all
eight. Before promising performance, **measure frontier width**
and transition cardinality; 4 states for one g chain do not imply
4 states for the three-chain join.

**Smallest previous missing lemma — COMPLETED (2026-11-03):**
`TaggedCarryWord.lean` proves that eight sequential
`taggedCarryStep` transitions reconstruct both the actual
32-bit base S-box output and its XOR derivative, with proper
carry propagation and rotation. No `sorry` or new `axiom`.

**First executable transfer + regressions — PROTOTYPED:**
`triple_carry_nibble_probe.py` verifies the one-nibble
three-carry factor against 512 full RFC g triples and replays
two already kernel-certified nontrivial five-round positive
trajectories. `toy_triple_exact_regression.py` builds a
true weighted finite-state transfer over two 4-bit nibbles
(using two RFC S-boxes, 8-bit addition, rotate-left-3).
Direct Feistel DDT, exact triple sum and weighted DP all give
**12** in one nonzero test, while the naive DDT convolution
gives **656** (coupling defect **644**).
A second test for the **same nonzero input and keys** has
true DDT **0**, exact weighted transfer **0**, yet the
naive convolution gives **40**. Toy transfer frontier
had **8** states for the positive case. The full 32-bit Magma DDT
has NOT yet been calculated with this DP.

**Rotate-left-11 local lemma — COMPLETED:**
`Rotate11Nibble.lean` proves the exact two-source nibble
wiring for any 32-bit word, and the same statement for
the emitted eight-element base/difference tag arrays.
It uses eight fixed-position bitvector proofs with
`bv_decide`, after unfolding the true BitVec nibble
operation. Also proves local reconstruction of the
completed eight-step tagged carry stream. No `sorry`.

**Exact real 32-bit conditional transfer — PROTOTYPED:**
`fixed_middle_transfer.py` fixes the middle word h and
inverts the middle round to determine its base z, reducing
the cyclic E/U boundary to **11 E bits plus six carries**.
It computes exact weighted conditional fiber counts
**16 and 96** for two real fixed-key Magma 5-round
positive witnesses. Independent Z3 exhaustion agrees.
The maximum observed frontier is **18**.
The degenerate a=b=0 case yields 2^32 as required.
`fixed_middle_subcube.py` sums over 256 h values:
**96 and 576**, also independently verified by #SMT.

**P0 remaining blocker:** eliminate h **inside** the
full-width transfer, rather than running it 2^32
times. The local count algorithm is still Python and
its weighted counting bijection is not yet kernel-proved.
Do not claim to have calculated the full five-round
DDT using the new transfer. See
`Magma/Composition/FIXED_MIDDLE_TRANSFER.md`.

## Priority P1 — reusable exact weighted composition, at a fixed key

Generalize the existing 5-round middle-fiber equivalence to
two arbitrary blocks with **one fixed schedule** and an explicit
shared full middle point `(base, difference)`.

The intended interface is a semiring-like kernel on finite
state/difference points, with composition

`(A ⋆ B)(p,r) = Σ_m A(p,m) * B(m,r)`.

The theorem must prove **equality of exact cardinalities**, with
correct key-window indexing and no overcount. Summing over full
`m` is exact; projecting `m` down to a coarser label is only
sound with a separate certified factorization/sufficient-statistic
condition. Keep this distinction visible in the API.

**Avoid a proof-only dead end:** also define a finite executable
representation for the kernel, perhaps a sparse weighted relation
indexed by the proposed carry-interface state. The mathematical
kernel over all full 64+64-bit labels is correct but not feasible
to materialize globally.

The generic arbitrary-n composition is conceptually straightforward;
its difficult part is **valid and efficient compression**, not the
formal algebra of a sum over all middle points.

## Priority P2 — regress five rounds BEFORE nine rounds

Run one executable exact local join with real RFC keys against
the already verified results:
- fixed-key five-round DDT/support for nonzero and zero cases;
- the `fiveRound_eq_sum_xor_correlations` and
  `fiveRound_eq_three_carry_traces` formulas;
- a case with a **provably strict coarse-label join defect**.
  This is crucial: a coincidental match on positive samples
  would not detect accidental multiplication of marginals;
- independent Rust/Python actual-state replay where feasible.

Deliver: one script/executable with small deterministic fixtures,
a count agreement report, and a Lean soundness/equality theorem
for the implemented transition, NOT thousands of concrete
certificates. If it still enumerates 32-bit `r,h`, optimization
has not succeeded.

## Priority P3 — reuse for 7/9+ and beyond

Only after passing P0-P2: apply the fixed-schedule composition to
the exact 7-round inner core of the 9-round outer slice
(`7 = 2 + 3 + 2`). Track both cut points with their complete
required labels or the proved compressed equivalent.
Use shared RFC key indices when overlapping windows demand it.
Report actual runtime, maximum frontier width, and eliminations
beyond the existing independent-support relaxation.

The first scientific goal is a **general reusable count/pruning
algorithm**, not an isolated nine-round UNSAT. New impossible
differentials may follow from its zero coefficients.

## Stop rules

- If a putative compressed state drops base/difference information
  and cannot reproduce a known 5-round strict-defect case:
  reject that representation, do not rationalize the mismatch.
- If intermediate frontier grows exponentially across nibbles:
  benchmark/record it and reconsider variable elimination order.
- If only the support predicate is computed, never label it an
  exact DDT count; distinguish support/positive count/weighted mass.
- No new 9+ long SAT matrix or bulk `decide` witness campaign
  until the 5-round exact executable prototype passes regression.
- A `sorry` or `axiom` may document an experimental gap in a
  separately named module; it is never evidence that the property
  was kernel-proved.

**Concrete first coding target:** the whole-word correctness lemma
for `GBaseTaggedCarryStep` followed by a prototype transfer table
for **one** small inverse-middle correlation block. This is the
highest-leverage bottom-up foundation for all four planned steps.
