module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundConvolutionDefect

@[expose] public section

/-!
# The right-output histogram of a three-round Magma differential

At fixed k₀,k₁,k₂,aL,aR,bL, the first two constraints define a finite
set of *concrete* candidate coordinates (R,Z). The third round assigns
**exactly one** right output difference to each such candidate.

Therefore the genuine three-round DDT, as bR varies, is the histogram
(pushforward) of that finite set. Its mass is exactly the already proved
two-function DDT convolution.

The bL = 0 specialization simplifies to the previously proved one-term
factorization; for nonzero bL the histogram retains the third-key coupling.
-/

namespace Magma.DiffanThreeRoundRightHistogram

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanThreeRoundConvolutionDefect

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- The right output difference resulting from a middle candidate `(R,Z)`.
    It is a *function* of the candidate, not another existential choice. -/
def rightOutput (k₀ k₁ k₂ aL aR bL : Word) (p : State) : Word :=
  xor (gDifference k₂ (xor (g k₁ p.2) p.1) bL)
    (intermediateDifference k₀ aL aR p.1)

/-- The final-round compatibility predicate is equality to the
    right-output label computed from the candidate. -/
theorem finalCondition_iff_rightOutput
    (k₀ k₁ k₂ aL aR bL bR : Word) (p : State) :
    finalCondition k₀ k₁ k₂ aL aR bL bR p ↔
      rightOutput k₀ k₁ k₂ aL aR bL p = bR := by
  let u := gDifference k₂ (xor (g k₁ p.2) p.1) bL
  let c := intermediateDifference k₀ aL aR p.1
  change (u = xor bR c) ↔ (xor u c = bR)
  change (u = bR ^^^ c) ↔ (u ^^^ c = bR)
  constructor
  · intro h
    rw [h]
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro h
    have hh := congrArg (fun v : Word => v ^^^ c) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh

/-- Middle candidates are precisely the coordinate pairs satisfying the
    middle-round constraint. -/
private theorem mem_middleCandidates_iff
    (k₀ k₁ aL aR bL : Word) (p : State) :
    p ∈ middleCandidates k₀ k₁ aL aR bL ↔
      middleCondition k₀ k₁ aL aR bL p := by
  classical
  unfold middleCandidates Diffan.FiberDefect.candidates
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

seal rightOutput middleCondition threeRoundCoupled middleCandidates

open scoped Classical in
/-- The actual three-round DDT is exactly one fiber of the right-output
    histogram on the middle-candidate set. -/
theorem actual_eq_rightOutput_fiber
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR) =
      ((middleCandidates k₀ k₁ aL aR bL).filter
        (fun p => rightOutput k₀ k₁ k₂ aL aR bL p = bR)).card := by
  classical
  rw [xorDDT_rounds_three]
  unfold threeRoundCoupledCount
  apply congrArg Finset.card
  ext p
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and,
    mem_middleCandidates_iff]
  exact (coupled_iff_middle_and_final k₀ k₁ k₂ aL aR bL bR p).trans
    (and_congr_right (fun _ => finalCondition_iff_rightOutput k₀ k₁ k₂ aL aR bL bR p))

open scoped Classical in
/-- The coupling defect is the complementary fiber of the same map. -/
theorem defect_eq_rightOutput_ne_fiber
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR bL bR =
      ((middleCandidates k₀ k₁ aL aR bL).filter
        (fun p => rightOutput k₀ k₁ k₂ aL aR bL p ≠ bR)).card := by
  classical
  unfold couplingDefect Diffan.FiberDefect.rejected
  apply congrArg Finset.card
  ext p
  change
    (p ∈ (Finset.univ : Finset State).filter
      (fun p => middleCondition k₀ k₁ aL aR bL p ∧
        ¬ finalCondition k₀ k₁ k₂ aL aR bL bR p)) ↔
    (p ∈ (middleCandidates k₀ k₁ aL aR bL).filter
      (fun p => rightOutput k₀ k₁ k₂ aL aR bL p ≠ bR))
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and,
    mem_middleCandidates_iff]
  exact and_congr_right (fun _ =>
    not_congr (finalCondition_iff_rightOutput k₀ k₁ k₂ aL aR bL bR p))

/- Partition a finite set into fibers of a label. -/
private theorem sum_fiber_card {X Y : Type*} [Fintype Y] [DecidableEq Y] (s : Finset X)
    (label : X → Y) : (∑ y : Y, (s.filter (fun x => label x = y)).card) = s.card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- MASS CONSERVATION: for any fixed left output difference, the total
    DDT mass over all right output differences is the two-round convolution.

    The third key changes the distribution of this mass, but not its sum. -/
theorem rightOutput_mass_eq_convolution
    (k₀ k₁ k₂ aL aR bL : Word) :
    (∑ bR : Word,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR)) =
      ∑ c : Word,
        xorDDT_g k₀ aR (xor c aL) *
          xorDDT_g k₁ c (xor bL aR) := by
  classical
  calc
    (∑ bR : Word,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR)) =
      ∑ bR : Word,
        ((middleCandidates k₀ k₁ aL aR bL).filter
          (fun p => rightOutput k₀ k₁ k₂ aL aR bL p = bR)).card := by
        apply Finset.sum_congr rfl
        intro bR _
        exact actual_eq_rightOutput_fiber k₀ k₁ k₂ aL aR bL bR
    _ = (middleCandidates k₀ k₁ aL aR bL).card :=
      sum_fiber_card (X := State) (Y := Word) (middleCandidates k₀ k₁ aL aR bL)
        (rightOutput k₀ k₁ k₂ aL aR bL)
    _ = _ := middleCandidates_card_eq_convolution k₀ k₁ aL aR bL

/-- A saturated convolution bound means *every* middle candidate is
    labeled by the same right-output difference. This criterion remains
    meaningful when bL ≠ 0. -/
theorem exact_iff_all_candidates_same_rightOutput
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
        (∑ c : Word,
          xorDDT_g k₀ aR (xor c aL) *
            xorDDT_g k₁ c (xor bL aR)) ↔
      ∀ p : State, middleCondition k₀ k₁ aL aR bL p →
        rightOutput k₀ k₁ k₂ aL aR bL p = bR := by
  rw [← middleCandidates_card_eq_convolution]
  constructor
  · intro h p hp
    have hf := (actual_eq_middle_iff k₀ k₁ k₂ aL aR bL bR).mp h p hp
    exact (finalCondition_iff_rightOutput k₀ k₁ k₂ aL aR bL bR p).mp hf
  · intro h
    apply (actual_eq_middle_iff k₀ k₁ k₂ aL aR bL bR).mpr
    intro p hp
    exact (finalCondition_iff_rightOutput k₀ k₁ k₂ aL aR bL bR p).mpr (h p hp)

/-- Existence of *some* realizable right output difference is equivalent
    to nonemptiness of the middle candidate set. This equivalence holds for
    bL = 0 and bL ≠ 0 alike. -/
theorem exists_rightOutput_iff_middle_nonempty
    (k₀ k₁ k₂ aL aR bL : Word) :
    (∃ bR : Word,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR)) ↔
      (middleCandidates k₀ k₁ aL aR bL).Nonempty := by
  classical
  constructor
  · rintro ⟨bR, hbR⟩
    rw [actual_eq_rightOutput_fiber] at hbR
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hbR
    exact ⟨p, (Finset.mem_filter.mp hp :
      p ∈ middleCandidates k₀ k₁ aL aR bL ∧
        rightOutput k₀ k₁ k₂ aL aR bL p = bR).1⟩
  · rintro ⟨p, hp⟩
    refine ⟨rightOutput k₀ k₁ k₂ aL aR bL p, ?_⟩
    rw [actual_eq_rightOutput_fiber]
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr (show
      p ∈ middleCandidates k₀ k₁ aL aR bL ∧
        rightOutput k₀ k₁ k₂ aL aR bL p = rightOutput k₀ k₁ k₂ aL aR bL p
      from ⟨hp, rfl⟩)⟩

/-- Projected support on the left output difference alone does not
    depend on the third round key, although individual right-output
    coefficients generally do. -/
theorem projected_support_independent_third_key
    (k₀ k₁ k₂ k₂' aL aR bL : Word) :
    (∃ bR : Word,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR)) ↔
    (∃ bR : Word,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂')
        (aL, aR) (bL, bR)) := by
  rw [exists_rightOutput_iff_middle_nonempty,
    exists_rightOutput_iff_middle_nonempty]

/-- The third key can redistribute right-output multiplicities but
    cannot change their total, at fixed input and left-output differences. -/
theorem rightOutput_mass_independent_third_key
    (k₀ k₁ k₂ k₂' aL aR bL : Word) :
    (∑ bR : Word,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (bL, bR)) =
    (∑ bR : Word,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂')
        (aL, aR) (bL, bR)) := by
  rw [rightOutput_mass_eq_convolution,
    rightOutput_mass_eq_convolution]

end Magma.DiffanThreeRoundRightHistogram
