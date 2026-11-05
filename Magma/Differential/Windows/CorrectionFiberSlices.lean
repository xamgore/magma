module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.AllKeyFeistelCorrection
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Exact right-state fibers of the second Feistel correction

For a fixed intermediate right difference `d`, the actual base `R` is
reparameterized by `x = R XOR d`. The second-round correction then becomes
precisely the XOR derivative of `g[k]` in direction `t` at `x`.

This gives an exact *conditional* cardinality result, even with an arbitrary
Boolean predicate on `x`. With an unrestricted predicate the fiber count is
exactly the existing `xorDDT_g k t b`.

The final two-witness theorem proves that for direction 0x6000 this correction
remains nonconstant for every key and **every fixed intermediate right
difference**, extending the earlier nonuniformity result for unrestricted
StateDifference pairs.

No claim is made that every intermediate state is reachable by a prescribed
prefix of Feistel rounds. Such a reachability restriction must be intersected
with the predicates in the existing scheduled meet framework.
-/

namespace Magma.DifanCorrectionFiberSlices

open Magma
open Magma.CarryAutomaton
open Magma.DifanFeistelDeltaPropagation

private abbrev Word :=
  V 32

private abbrev Point :=
  Difan.StateDifference (Word × Word) (Word × Word)

/-- A midpoint with fixed right difference `d` and variable right base `R`.
    Left components are irrelevant to the second-round correction. -/
def sampleMid (R d : Word) : Point :=
  ⟨(0#32, R), (0#32, d)⟩

/-- An arbitrary Boolean restriction on the derivative's actual base `x`.
    Here `R = x XOR d`; hence `P` is tested on `R XOR d`. -/
def correctionCountIf (k t d b : Word) (P : Word → Bool) : Nat :=
  ((Finset.univ : Finset Word).filter (fun R =>
    P (R ^^^ d) = true ∧ secondCorrection k t (sampleMid R d) = b)).card

/-- The corresponding *actual* one-round XOR-derivative fiber. -/
def derivativeCountIf (k t b : Word) (P : Word → Bool) : Nat :=
  ((Finset.univ : Finset Word).filter (fun x =>
    P x = true ∧ (g k (x ^^^ t) ^^^ g k x) = b)).card

private theorem xor_cancel_right (x d : Word) : (x ^^^ d) ^^^ d = x := by
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem xor_change_of_base (x d t : Word) : (x ^^^ d) ^^^ (d ^^^ t) = x ^^^ t := by
  bv_decide

/-- The change of coordinates `R ↦ R XOR d` is a bijection of conditional
    *real-base-state* fibers, not merely an equality of abstract supports. -/
theorem correctionCountIf_eq_derivativeCountIf
    (k t d b : Word) (P : Word → Bool) :
    correctionCountIf k t d b P = derivativeCountIf k t b P := by
  classical
  unfold correctionCountIf derivativeCountIf
  apply Finset.card_bij (fun R _ => R ^^^ d)
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    refine ⟨hR.1, ?_⟩
    have hEq : g k (R ^^^ (d ^^^ t)) ^^^ g k (R ^^^ d) = b := hR.2
    change g k ((R ^^^ d) ^^^ t) ^^^ g k (R ^^^ d) = b
    rw [← BitVec.xor_assoc] at hEq
    exact hEq
  · intro R _ R' _ h
    have hh := congrArg (fun x : Word => x ^^^ d) h
    simpa only [xor_cancel_right] using hh
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x ^^^ d, ?_, xor_cancel_right x d⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simpa only [xor_cancel_right] using hx.1
    · change g k ((x ^^^ d) ^^^ (d ^^^ t)) ^^^
        g k ((x ^^^ d) ^^^ d) = b
      rw [xor_change_of_base x d t, xor_cancel_right x d]
      exact hx.2

/-- Removing the state filter gives the DDT coefficient in direction `t`,
    independently of the fixed intermediate difference `d`. -/
theorem correctionCount_eq_xorDDT (k t d b : Word) :
    correctionCountIf k t d b (fun _ => true) = xorDDT_g k t b := by
  have h := correctionCountIf_eq_derivativeCountIf
    k t d b (fun _ => true)
  simpa [derivativeCountIf, xorDDT_g, Magma.xor] using h

/-- In particular, the set of correction values possible at any fixed `d`
    is exactly the support of the corresponding XOR-DDT row. -/
theorem correctionCount_positive_iff (k t d b : Word) :
    0 < correctionCountIf k t d b (fun _ => true) ↔
      0 < xorDDT_g k t b := by
  rw [correctionCount_eq_xorDDT]

/-- Choosing a derivative base `x` directly gives a genuine midpoint
    with the prescribed right difference `d`. -/
def midAt (d x : Word) : Point := sampleMid (x ^^^ d) d

/-- The value of the correction at `midAt d x` is independent of `d`:
    `d` changes the coordinate system, not the local XOR derivative. -/
theorem correction_midAt (k t d x : Word) :
    secondCorrection k t (midAt d x) =
      g k (x ^^^ t) ^^^ g k x := by
  change g k ((x ^^^ d) ^^^ (d ^^^ t)) ^^^
    g k ((x ^^^ d) ^^^ d) = _
  rw [xor_change_of_base x d t, xor_cancel_right x d]

/-- The previously proved 16-case S-box obstruction persists at every fixed
    intermediate right difference and for every key. -/
theorem shift6000_distinct_on_each_right_difference (k d : Word) :
    secondCorrection k (0x00006000#32) (midAt d (0#32)) ≠
      secondCorrection k (0x00006000#32)
        (midAt d (0x00001000#32)) := by
  rw [correction_midAt, correction_midAt]
  have hxor : ((0x00001000#32 : Word) ^^^ (0x00006000#32)) =
      (0x00007000#32 : Word) := by decide
  simpa only [BitVec.zero_xor, hxor] using
    Magma.DifanAllKeyFeistelCorrection.shift6000_two_witnesses k

/-- Therefore no value `b` can describe the correction on all midpoints
    with the same right difference `d` (even if the key is fixed). -/
theorem shift6000_not_constant_at_fixed_right_difference
    (k d b : Word) :
    ¬ ∀ R : Word,
      secondCorrection k (0x00006000#32) (sampleMid R d) = b := by
  intro h
  have hzero :
      secondCorrection k (0x00006000#32) (midAt d (0#32)) = b :=
    h ((0#32) ^^^ d)
  have hone :
      secondCorrection k (0x00006000#32)
        (midAt d (0x00001000#32)) = b :=
    h ((0x00001000#32) ^^^ d)
  exact (shift6000_distinct_on_each_right_difference k d)
    (hzero.trans hone.symm)

/-- The right correction is independent of both left midpoint coordinates.
    Thus the preceding obstruction also holds with any fixed left base and
    left difference; only the right base varies. -/
theorem correction_left_coordinates_irrelevant
    (k t L aL R d : Word) :
    secondCorrection k t (⟨(L, R), (aL, d)⟩ : Point) =
      secondCorrection k t (sampleMid R d) := rfl

end Magma.DifanCorrectionFiberSlices
