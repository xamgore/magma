module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundCouplingDefect
public import Magma.Differential.ThreeRounds.ThreeRoundCoordinateCertificate

@[expose] public section

/-!
# Three-round convolution and exact coupling loss

The convolution of two round-function DDTs counts trajectories satisfying
the middle-round condition. The final-round condition rejects exactly
`couplingDefect` of these witnesses, so the convolution equals the actual
three-round DDT plus that defect.

For zero left output difference, the accepted count is one convolution
summand. The other intermediate differences account for the entire defect.
-/

namespace Magma.DiffanThreeRoundConvolutionDefect

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- Cancel a fixed right XOR operand; needed only to identify the
    middle-round condition with the standard XOR-DDT predicate. -/
private theorem xor_right_iff_local (u a b : Word) :
    xor u a = b ↔ u = xor b a := by
  change (u ^^^ a = b) ↔ (u = b ^^^ a)
  constructor
  · intro h
    have h' := congrArg (fun v : Word => v ^^^ a) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using h'
  · intro h
    rw [h]
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

open scoped Classical in
/-- At a *fixed* first coordinate R, the number of admissible second
    coordinates Z is exactly a round-function DDT entry. -/
private theorem middleFiber_card (k₀ k₁ aL aR bL R : Word) :
    ((Finset.univ : Finset Word).filter
      (fun Z => middleCondition k₀ k₁ aL aR bL (R, Z))).card =
        xorDDT_g k₁ (intermediateDifference k₀ aL aR R) (xor bL aR) := by
  classical
  unfold xorDDT_g
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro Z _
  change
    (xor (gDifference k₁ Z (intermediateDifference k₀ aL aR R)) aR = bL) ↔
      (gDifference k₁ Z (intermediateDifference k₀ aL aR R) = xor bL aR)
  exact xor_right_iff_local _ _ _

/-- Counting the middle candidates does not require the third key or the
    target right-half difference. It is the exact sum over the first
    coordinate of the second round-function DDT. -/
theorem middleCandidates_card_eq_sum
    (k₀ k₁ aL aR bL : Word) :
    (middleCandidates k₀ k₁ aL aR bL).card =
      ∑ R : Word,
        xorDDT_g k₁ (intermediateDifference k₀ aL aR R) (xor bL aR) := by
  classical
  calc
    (middleCandidates k₀ k₁ aL aR bL).card =
        ∑ R : Word, ∑ Z : Word,
          if middleCondition k₀ k₁ aL aR bL (R, Z) then (1 : Nat) else 0 := by
      unfold middleCandidates Diffan.FiberDefect.candidates
      rw [Finset.card_filter, Fintype.sum_prod_type]
    _ = ∑ R : Word,
          xorDDT_g k₁ (intermediateDifference k₀ aL aR R) (xor bL aR) := by
      apply Finset.sum_congr rfl
      intro R _
      calc
        (∑ Z : Word,
          if middleCondition k₀ k₁ aL aR bL (R, Z) then (1 : Nat) else 0) =
            ((Finset.univ : Finset Word).filter
              (fun Z => middleCondition k₀ k₁ aL aR bL (R, Z))).card := by
          rw [Finset.card_filter]
        _ = _ := middleFiber_card k₀ k₁ aL aR bL R

/-- The candidate count is the exact convolution proved earlier in
    `Magma.MultiRoundDDT`, regrouped by intermediate difference c. -/
theorem middleCandidates_card_eq_convolution
    (k₀ k₁ aL aR bL : Word) :
    (middleCandidates k₀ k₁ aL aR bL).card =
      ∑ c : Word,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c (xor bL aR) := by
  rw [middleCandidates_card_eq_sum]
  exact threeRound_middle_sum_eq_convolution k₀ k₁ aL aR bL

/-- The convolution partitions into accepted trajectories and the exact coupling loss. -/
theorem actual_add_defect_eq_convolution
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR) +
      couplingDefect k₀ k₁ k₂ aL aR bL bR =
        ∑ c : Word,
          xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c (xor bL aR) := by
  calc
    _ = (middleCandidates k₀ k₁ aL aR bL).card :=
      actual_add_defect_eq_middle k₀ k₁ k₂ aL aR bL bR
    _ = _ := middleCandidates_card_eq_convolution k₀ k₁ aL aR bL

/-- Convolution upper bound with its exact residual, explicitly. -/
theorem couplingDefect_eq_convolution_sub_actual
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR bL bR =
      (∑ c : Word,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c (xor bL aR)) -
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) := by
  have h := actual_add_defect_eq_convolution k₀ k₁ k₂ aL aR bL bR
  omega

/-- Vanishing coupling loss characterizes sharpness of the convolution bound. -/
theorem actual_eq_convolution_iff_defect_zero
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (bL, bR) =
      (∑ c : Word,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c (xor bL aR)) ↔
      couplingDefect k₀ k₁ k₂ aL aR bL bR = 0 := by
  have h := actual_add_defect_eq_convolution k₀ k₁ k₂ aL aR bL bR
  omega

/-- In the already factorized zero-left slice, the coupling defect is
    precisely the rest of the convolution beyond the single product. -/
theorem zeroLeft_defect_eq_convolution_sub_product
    (k₀ k₁ k₂ aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      (∑ c : Word,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR) -
      xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR := by
  have h := actual_add_defect_eq_convolution
    k₀ k₁ k₂ aL aR (0#32) bR
  have hf := Magma.DiffanThreeRoundCoordinateCertificate.threeRound_factorization_via_coordinates
    k₀ k₁ k₂ aL aR bR
  have hz : xor (0#32) aR = aR := by
    change (0#32) ^^^ aR = aR
    exact BitVec.zero_xor
  rw [hf, hz] at h
  omega

/-- Stronger zero-left formula: the defect is EXACTLY the sum of
    contributions from the "wrong" intermediate differences c ≠ bR.

    Hence the three-round factorization selects the single surviving
    diagonal summand of the two-round convolution. -/
theorem zeroLeft_defect_eq_offDiagonal
    (k₀ k₁ k₂ aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      ∑ c ∈ (Finset.univ : Finset Word).erase bR,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR := by
  classical
  have h := actual_add_defect_eq_convolution
    k₀ k₁ k₂ aL aR (0#32) bR
  have hf := Magma.DiffanThreeRoundCoordinateCertificate.threeRound_factorization_via_coordinates
    k₀ k₁ k₂ aL aR bR
  have hz : xor (0#32) aR = aR := by
    change (0#32) ^^^ aR = aR
    exact BitVec.zero_xor
  rw [hf, hz] at h
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset Word)
    (fun c : Word => xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR)
    (Finset.mem_univ bR)
  have htotal :
      xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR +
        couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      (∑ c ∈ (Finset.univ : Finset Word).erase bR,
        xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR) +
        xorDDT_g k₀ aR (xor bR aL) * xorDDT_g k₁ bR aR := by
    exact h.trans hsplit.symm
  omega

/-- In the zero-left slice the rejected candidate count does not depend
    on the third round key: the final condition fixes the intermediate
    difference instead of constraining the third round function. -/
theorem zeroLeft_defect_independent_third_key
    (k₀ k₁ k₂ k₂' aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      couplingDefect k₀ k₁ k₂' aL aR (0#32) bR := by
  rw [zeroLeft_defect_eq_offDiagonal, zeroLeft_defect_eq_offDiagonal]

/-- When every other intermediate-difference summand vanishes, the
    two-round convolution upper bound is already exact in the zero-left slice. -/
theorem zeroLeft_defect_zero_of_offDiagonal_zero
    (k₀ k₁ k₂ aL aR bR : Word)
    (h : ∀ c : Word, c ≠ bR →
      xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR = 0) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR = 0 := by
  rw [zeroLeft_defect_eq_offDiagonal]
  apply Finset.sum_eq_zero
  intro c hc
  exact h c (Finset.mem_erase.mp hc).1

end Magma.DiffanThreeRoundConvolutionDefect
