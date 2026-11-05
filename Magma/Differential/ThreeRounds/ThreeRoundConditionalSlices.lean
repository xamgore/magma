module

import all Init.Data.Range.Basic
public import Diffan.Fibers.FiberUniformity
public import Magma.Differential.ThreeRounds.ThreeRoundRightHistogram

@[expose] public section

/-!
# Conditional fibers of the three-round right-output histogram

The previously proved 3-round DDT histogram is now decomposed by the
first-round intermediate difference c and then the concrete first
coordinate R. The remaining Z-count is *conditional on R*, so the formula
is exact without assuming independence. A second theorem states the
precise, separately provable homogeneity condition under which a new
DDT-style convolution really follows.
-/

namespace Magma.DiffanThreeRoundConditionalSlices

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanThreeRoundRightHistogram
open Magma.DiffanThreeRoundCoordinateCertificate

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

attribute [local instance 2000] Classical.propDecidable

/-- Exact Z-fiber at a fixed R (not a standalone round-function DDT). -/
noncomputable def conditionalZCount (k₀ k₁ k₂ aL aR bL bR R : Word) : Nat :=
  Diffan.FiberUniformity.conditionalCount
    (fun R Z => middleCondition k₀ k₁ aL aR bL (R, Z))
    (fun R Z => rightOutput k₀ k₁ k₂ aL aR bL (R, Z) = bR)
    R

open scoped Classical in
/-- Combine the middle-round and right-output conditions on their shared
    concrete coordinates. -/
private theorem histogram_as_joint_filter
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    ((middleCandidates k₀ k₁ aL aR bL).filter
      (fun p => rightOutput k₀ k₁ k₂ aL aR bL p = bR)).card =
    ((Finset.univ : Finset State).filter
      (fun p => middleCondition k₀ k₁ aL aR bL p ∧
        rightOutput k₀ k₁ k₂ aL aR bL p = bR)).card := by
  classical
  apply congrArg Finset.card
  ext p
  simp only [middleCandidates, Diffan.FiberDefect.candidates,
    Finset.mem_filter, Finset.mem_univ, true_and]

seal Finset.univ middleCondition rightOutput intermediateDifference

/-- EXACT conditioned sum, valid for all keys and all input/output
    differences, including nonzero output-left differences.

    `conditionalZCount ... R` generally depends on R even when
    `intermediateDifference ... R = c` is fixed. -/
theorem ddt_eq_sum_conditional_slices
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
    ∑ c : Word, ∑ R : Word,
      if intermediateDifference k₀ aL aR R = c then
        conditionalZCount k₀ k₁ k₂ aL aR bL bR R
      else 0 := by
  classical
  rw [actual_eq_rightOutput_fiber,
    histogram_as_joint_filter]
  simpa only [Prod.eta, conditionalZCount] using
    (Diffan.FiberUniformity.card_eq_sum_slices
    (fun R Z => middleCondition k₀ k₁ aL aR bL (R, Z))
    (fun R Z => rightOutput k₀ k₁ k₂ aL aR bL (R, Z) = bR)
    (intermediateDifference k₀ aL aR))

/-! XOR cancellation identifies each intermediate-difference class
with a first-round DDT fiber. -/

private theorem xor_right_eq_iff (u a b : Word) : xor u a = b ↔ u = xor b a := by
  change (u ^^^ a = b) ↔ (u = b ^^^ a)
  constructor
  · intro h
    have hh := congrArg (fun v : Word => v ^^^ a) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh
  · intro h
    rw [h]
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

open scoped Classical in
/-- Symbolic cardinality of the first-coordinate class of c. -/
theorem intermediate_class_card
    (k₀ aL aR c : Word) :
    ((Finset.univ : Finset Word).filter
      (fun R => intermediateDifference k₀ aL aR R = c)).card =
      xorDDT_g k₀ aR (xor c aL) := by
  classical
  unfold xorDDT_g
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro R _
  unfold intermediateDifference
  exact xor_right_eq_iff (gDifference k₀ R aR) aL c

/-- Conditioning on the final round can only remove Z-witnesses.
    Thus even before finding a homogeneous class, each individual
    conditional count is bounded by the middle-round-function DDT. -/
theorem conditionalZCount_le_middleDDT
    (k₀ k₁ k₂ aL aR bL bR R : Word) :
    conditionalZCount k₀ k₁ k₂ aL aR bL bR R ≤
      xorDDT_g k₁ (intermediateDifference k₀ aL aR R) (xor bL aR) := by
  classical
  calc
    conditionalZCount k₀ k₁ k₂ aL aR bL bR R ≤
        ((Finset.univ : Finset Word).filter
          (fun Z => middleCondition k₀ k₁ aL aR bL (R, Z))).card := by
      unfold conditionalZCount Diffan.FiberUniformity.conditionalCount
      simp only
      apply Finset.card_le_card
      apply Finset.monotone_filter_right
      intro Z _ hZ
      exact hZ.1
    _ = xorDDT_g k₁ (intermediateDifference k₀ aL aR R)
          (xor bL aR) := by
      unfold xorDDT_g
      apply congrArg Finset.card
      ext Z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold middleCondition
      change (xor (gDifference k₁ Z (intermediateDifference k₀ aL aR R)) aR = bL) ↔
        (gDifference k₁ Z (intermediateDifference k₀ aL aR R) = xor bL aR)
      exact xor_right_eq_iff _ _ _

/-- PRECISE CONDITION FOR NEW FACTORIZATION.
    When the conditional Z-cardinality depends only on the intermediate
    difference c, the exact three-round DDT becomes a weighted convolution. -/
theorem ddt_eq_weighted_convolution_of_uniform
    (k₀ k₁ k₂ aL aR bL bR : Word)
    (weight : Word → Nat)
    (uniform : ∀ c R : Word,
      intermediateDifference k₀ aL aR R = c →
      conditionalZCount k₀ k₁ k₂ aL aR bL bR R = weight c) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
    ∑ c : Word,
      xorDDT_g k₀ aR (xor c aL) * weight c := by
  classical
  let : DecidableEq Word := fun a b => Classical.propDecidable (a = b)
  rw [ddt_eq_sum_conditional_slices]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ R : Word,
      if intermediateDifference k₀ aL aR R = c then
        conditionalZCount k₀ k₁ k₂ aL aR bL bR R
      else 0) =
        ∑ R : Word,
          if intermediateDifference k₀ aL aR R = c then weight c else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      by_cases h : intermediateDifference k₀ aL aR R = c
      · simp only [ite_eq_left h]
        exact uniform c R h
      · simp only [ite_eq_right h]
    _ = ((Finset.univ : Finset Word).filter
          (fun R => intermediateDifference k₀ aL aR R = c)).card * weight c := by
      rw [Finset.card_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R _
      by_cases h : intermediateDifference k₀ aL aR R = c <;> simp [h]
    _ = xorDDT_g k₀ aR (xor c aL) * weight c := by
      have hclass := intermediate_class_card k₀ aL aR c
      rw [← hclass]
      apply congrArg (fun s : Finset Word => s.card * weight c)
      ext R
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Magma.DiffanThreeRoundConditionalSlices
