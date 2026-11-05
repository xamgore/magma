module

import all Init.Data.Range.Basic
public import Difan.Core.CoordinateSeparation
public import Magma.Differential.ThreeRounds.ThreeRoundPeriodOrbits

@[expose] public section

/-!
# Exact three-round factorization for zero right input difference

The known zero-LEFT-output factorization removes the THIRD round key.
This *different* slice, with zero RIGHT input difference, removes the
FIRST round key and separates the remaining middle and last round tests.

For all fixed round keys and 32-bit differences:

  D₃ ((aL, 0), (bL, bR))
    = D_{g[k₁]} (aL, bL) * D_{g[k₂]} (bL, bR XOR aL).

The proof is structural. In the existing independent coordinates (R,Z),
use the bijection (R,Z) ↦ (Z, R XOR g[k₁](Z)). Both compatibility tests
then depend on separate coordinates.
-/

namespace Magma.DifanThreeRoundZeroRightInputFactorization

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- Another bijective coordinate chart on the 64-bit witness space:
    (R,Z) ↦ (Z, g[k₁](Z) XOR R). -/
def zeroRightCoordinates (k₁ : Word) : State ≃ State where
  toFun := fun p => (p.2, xor (g k₁ p.2) p.1)
  invFun := fun p => (xor (g k₁ p.1) p.2, p.1)
  left_inv := by
    rintro ⟨R, Z⟩
    apply Prod.ext
    · change (g k₁ Z ^^^ (g k₁ Z ^^^ R)) = R
      simp only [← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor]
    · rfl
  right_inv := by
    rintro ⟨Z, Y⟩
    apply Prod.ext
    · rfl
    · change (g k₁ Z ^^^ (g k₁ Z ^^^ Y)) = Y
      simp only [← BitVec.xor_assoc, BitVec.xor_self,
        BitVec.zero_xor]

/-- A zero input difference gives a zero concrete XOR derivative. -/
theorem gDifference_zero (k R : Word) :
    gDifference k R (0#32) = (0#32) := by
  unfold gDifference
  change (g k (R ^^^ (0#32))) ^^^ g k R = (0#32)
  simp only [BitVec.xor_zero, BitVec.xor_self]

/-- Thus c(R) ceases to depend on the first key or the base word R. -/
theorem intermediateDifference_zero_right (k₀ aL R : Word) :
    intermediateDifference k₀ aL (0#32) R = aL := by
  unfold intermediateDifference
  rw [gDifference_zero]
  change (0#32) ^^^ aL = aL
  exact BitVec.zero_xor

/-- First compatibility condition depends only on Z. -/
theorem middleCondition_zero_right_iff
    (k₀ k₁ aL bL : Word) (p : State) :
    middleCondition k₀ k₁ aL (0#32) bL p ↔
      gDifference k₁ (zeroRightCoordinates k₁ p).1 aL = bL := by
  unfold middleCondition
  rw [intermediateDifference_zero_right]
  change (gDifference k₁ p.2 aL ^^^ (0#32) = bL) ↔
    (gDifference k₁ p.2 aL = bL)
  simp only [BitVec.xor_zero]

/-- Final compatibility condition depends only on the new Y coordinate. -/
theorem finalCondition_zero_right_iff
    (k₀ k₁ k₂ aL bL bR : Word) (p : State) :
    finalCondition k₀ k₁ k₂ aL (0#32) bL bR p ↔
      gDifference k₂ (zeroRightCoordinates k₁ p).2 bL =
        xor bR aL := by
  unfold finalCondition
  rw [intermediateDifference_zero_right]
  rfl

/-- The complete three-round predicate separates into independent
    Z and Y conditions after this *specific* change of coordinates. -/
theorem zeroRightInput_separates
    (k₀ k₁ k₂ aL bL bR : Word) (p : State) :
    threeRoundCoupled k₀ k₁ k₂ aL (0#32) bL bR p.1 p.2 ↔
      gDifference k₁ (zeroRightCoordinates k₁ p).1 aL = bL ∧
      gDifference k₂ (zeroRightCoordinates k₁ p).2 bL =
        xor bR aL := by
  have hc := coupled_iff_middle_and_final
    k₀ k₁ k₂ aL (0#32) bL bR p
  have hm := middleCondition_zero_right_iff k₀ k₁ aL bL p
  have hf := finalCondition_zero_right_iff k₀ k₁ k₂ aL bL bR p
  constructor
  · intro h
    exact ⟨hm.mp (hc.mp h).1, hf.mp (hc.mp h).2⟩
  · rintro ⟨hz, hy⟩
    exact hc.mpr ⟨hm.mpr hz, hf.mpr hy⟩

/-- The exact witness set is equivalent to a product of two ordinary
    round-function differential fibers. -/
def zeroRightInput_fiberEquiv
    (k₀ k₁ k₂ aL bL bR : Word) :
    {p : State // threeRoundCoupled k₀ k₁ k₂
      aL (0#32) bL bR p.1 p.2} ≃
    {Z : Word // gDifference k₁ Z aL = bL} ×
    {Y : Word // gDifference k₂ Y bL = xor bR aL} :=
  Difan.CoordinateSeparation.fiberEquiv
    (zeroRightCoordinates k₁)
    (fun p => threeRoundCoupled k₀ k₁ k₂
      aL (0#32) bL bR p.1 p.2)
    (fun Z => gDifference k₁ Z aL = bL)
    (fun Y => gDifference k₂ Y bL = xor bR aL)
    (zeroRightInput_separates k₀ k₁ k₂ aL bL bR)

open scoped Classical in
/-- A derivative fiber has the cardinality of its round-function DDT entry. -/
theorem gDifference_fiber_card (k d out : Word) :
    Fintype.card {x : Word // gDifference k x d = out} =
      xorDDT_g k d out := by
  classical
  calc
    Fintype.card {x : Word // gDifference k x d = out} =
        ((Finset.univ : Finset Word).filter
          (fun x => gDifference k x d = out)).card :=
      Fintype.card_subtype (fun x : Word => gDifference k x d = out)
    _ = xorDDT_g k d out := by
      unfold xorDDT_g
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro x _
      rfl

/-- SECOND EXACT THREE-ROUND FACTORIZATION.

    In contrast to zero-left-output factorization, this slice is
    independent of the *first* round key, not of the third.
    Both factors are genuine fixed-key DDT counts. -/
theorem threeRound_zeroRightInput_factorization
    (k₀ k₁ k₂ aL bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, (0#32)) (bL, bR) =
      xorDDT_g k₁ aL bL * xorDDT_g k₂ bL (xor bR aL) := by
  classical
  calc
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, (0#32)) (bL, bR) =
        threeRoundCoupledCount k₀ k₁ k₂ aL (0#32) bL bR :=
      xorDDT_rounds_three k₀ k₁ k₂ aL (0#32) bL bR
    _ = Fintype.card {p : State // threeRoundCoupled k₀ k₁ k₂
        aL (0#32) bL bR p.1 p.2} := by
      unfold threeRoundCoupledCount
      rw [Fintype.card_subtype]
    _ = Fintype.card {Z : Word // gDifference k₁ Z aL = bL} *
        Fintype.card {Y : Word // gDifference k₂ Y bL = xor bR aL} := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr
        (zeroRightInput_fiberEquiv k₀ k₁ k₂ aL bL bR)
    _ = xorDDT_g k₁ aL bL * xorDDT_g k₂ bL (xor bR aL) := by
      rw [gDifference_fiber_card, gDifference_fiber_card]

/-- The entire zero-right-input slice is insensitive to k₀. -/
theorem zeroRightInput_independent_first_key
    (k₀ k₀' k₁ k₂ aL bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, (0#32)) (bL, bR) =
      xorDDT_rounds 3 (threeRoundKeys k₀' k₁ k₂)
        (aL, (0#32)) (bL, bR) := by
  rw [threeRound_zeroRightInput_factorization,
    threeRound_zeroRightInput_factorization]

/-- If either independent local fiber is empty, the three-round
    differential has no witnesses. -/
theorem zeroRightInput_zero_of_first_zero
    (k₀ k₁ k₂ aL bL bR : Word)
    (h : xorDDT_g k₁ aL bL = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, (0#32)) (bL, bR) = 0 := by
  rw [threeRound_zeroRightInput_factorization, h, zero_mul]

theorem zeroRightInput_zero_of_second_zero (k₀ k₁ k₂ aL bL bR : Word)
    (h : xorDDT_g k₂ bL (xor bR aL) = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, (0#32)) (bL, bR) = 0 := by
  rw [threeRound_zeroRightInput_factorization, h, mul_zero]

end Magma.DifanThreeRoundZeroRightInputFactorization
