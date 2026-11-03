# Sparse windows: research status and decision points

> Active nine-round research, Lean models, scripts and fixtures have
> moved to `Magma/NinePlus/README.md`. This file remains
> a broader index and history of earlier sparse-difference studies.

This is the **current** guide for the Magma differential project. The older
append-only chronology is in `research/archive/SPARSE_WINDOWS_HISTORY.md`.
The archive contains earlier hypotheses and intermediate outcomes, some
superseded by later experiments. It is not the source of current claims.

## Big picture

The exact two-sided Feistel boundary identity is, for any fixed n+2
ordinary round keys,

```text
D_(n+2) ((a,0), (0,s)) = D_n^inner ((0,a), (s,0))
```

where the inner n round keys are the original keys 1,...,n.
This is an exact equality of DDT **counts**, not a Markov assumption.
See `FirstRoundDeletion.lean`. It reduces outer 8 rounds to a
six-round inner problem, and similarly for arbitrary n+2 rounds.
It does not claim the inner slice is again of outer form.

The `OuterWordRecurrence.lean` and `IndependentRoundSupport.lean`
modules formulate increasingly strong **necessary** conditions
for an n-round inner difference. Failure of either condition gives
an actual Magma DDT zero for *every* fixed sequence of round keys.
Positive local support alone does not imply any true full-round
trajectory, because the per-round base states may be incompatible.

## Eight-round forbidden rectangles: priority is CONDITIONAL

For an eight-round outer slice the experimentally excluded rectangles
are nibble-index pairs (5,7), (6,7), (7,5), (7,6), (7,7), counting
nibbles from the least-significant end. Each endpoint is a **nonzero**
32-bit word supported entirely within that single four-bit nibble.
Thus 5*15*15 = 1125 distinct *candidate* zeros.

The experiment `research/outer8_local_support_z3.py` refutes even a
relaxation in which each of the six actual inner g-derivatives may pick
its own independent key and base word. That experiment returned UNSAT
for all five unrestricted 4-bit-value rectangles, not just 80 one-hot
cells. These statements are **Z3 computational outcomes, not Lean
UNSAT proofs**. The weaker first-active-nibble-only filter does not
exclude those representative cells.

Lean does prove `eight_round_outer_zero_of_no_six_local_support`,
`six_independent_core_symmetric` and
`eight_round_zero_of_rejected_rectangle`. Consequently three
independent still-open rectangle obligations (5,7), (6,7), (7,7)
would imply all five, without a master-key-independence assumption.
The missing proofs are explicit parameters; no axioms/sorry were added.

### Where a certified 8-round zero could be used

For a longer m+8+r trajectory, split its difference path at the
eight-round window. An eight-round no-go theorem can eliminate the
whole path **only if every possible pair of intermediate cut
differences is in one of the forbidden rectangles, with the required
zero half-windows**. Formally the necessary cut is

```text
  Path m alpha u   AND
  (u = (a,0), v = (0,s), a/s in forbidden rectangle)   AND
  Path r v omega
```

or the analogous stronger correlated-path predicate. A forbidden
inner eight-round edge can prune a DP/graph search, a truncated
differential enumeration, or a meet-in-the-middle join.
A zero in the special outer slice cannot be blindly pasted into an
arbitrary 9-, 12-, or 16-round endpoint theorem.

**Decision gate:** before proving the three remaining UNSAT
certificates, test whether adding the five forbidden rectangles to
a multi-round search actually removes any transitions that survive
the existing nibble/word support filter. Measure cells eliminated,
runtime, and surviving false positives. If the gain is negligible,
retain the Z3 experiment and conditional Lean soundness results,
and **defer** the expensive certification.

If there is meaningful gain, prove a *reusable nibble/carry checker*
and a compact, Lean-checkable refutation for the three independent
rectangles, rather than manually writing hundreds of lemmas.

## Nine-round one-hot positives: CLOSED, low research priority

The full family `(2^i,0) -> (0,2^j)` for 0<=i,j<32 has 1024
concrete SAT witnesses, and the corresponding `∃ master, ∃ base`
statement is already checked by the Lean kernel.
This proves **there exists SOME RFC 8891 master key per pair**.
It does not say a single fixed master key realizes all 1024 cells.
It establishes a boundary for the special family, but does not
explain its algebraic structure. Do **not** expand this exercise to
other large witness matrices without a direct scientific application.

The 128 generated witness modules, 32 row lemmas, and final theorem
are retained under `Magma/Diffan/NineRoundPositiveRows` and
`NineRoundAllOneHotPositive.lean`. They are opt-in and are excluded
from the ordinary `Magma` import. To check them:

```bash
lake build Magma.Diffan.Certificates
```

Generator: `research/generate_nine_onehot_lean.py --all`.
The source witness matrix is in the ignored
`research/nround_runs/onehot32_9` directory; generated Lean
certificates are tracked by Git, so they stay checkable without it.

## Other known boundaries and experimental tools

- Five-round 2-hot -> 2-hot outer: 246016 UNSAT results from the
  exhaustive SAT run, **not** a universal Lean proof. Certified
  structural subfamilies exist. Keep these statuses distinct.
- The parameterized `research/magma_exact_matrix_nround.rs`
  evaluates 5..32 ordinary rounds using the single symbolic master
  key schedule and directly replays positive witnesses.
- `research/verify_nround.py` independently replays all positive
  models and verifies compressed matrix hashes.
- `research/outer8_local_support_z3.py` checks the stronger
  key/base-independent six-inner-round support relaxation.
- `Magma/Diffan/CorrelatedFiveMacro.lean` retains **real base-state
  correlation** for a five-round window; it is more suitable when
  support-only relaxations prove too weak.

## Next experiment (before any heavy Lean proof)

1. Add a lightweight *hypothetical* eight-round forbidden-edge
   predicate to the existing path/DP scanner; do not pretend the
   Z3 rectangles are formally certified.
2. Compare with/without these edges on actual 10..16-round sparse
   boundary classes. Report surviving possibilities and cost.
3. If that produces a meaningful new long-round impossible family,
   formalize the cut theorem and only then generate a compact
   UNSAT proof certificate for the three rectangle obligations.
4. Otherwise prioritize a more general correlated carry/base
   transducer. Avoid bulk positive witness formalization.

Proof priority, classification and stop rules for the whole project:
`research/PROOF_POLICY.md`.
