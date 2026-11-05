module

import all Init.Data.Range.Basic
public import Diffan.Fibers.FiberDefect
public import Magma.Differential.Core.MultiRoundDDT

@[expose] public section

/-!
# Magma.Diffan.ThreeRoundCouplingDefect

A general three-round output (not necessarily zero-left) has two separate
conditions in the coordinates `(R,Z)`. The first is the middle-round
condition. The second is the compatibility imposed by the third round.

The number passing the first condition is exactly the number passing
both conditions PLUS the number rejected by the third-round condition.
This measures the structural *defect* of the naive two-round upper bound.
-/

namespace Magma.DiffanThreeRoundCouplingDefect

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- The intermediate difference after the first round, as a function of R. -/
def intermediateDifference (k₀ aL aR R : Word) : Word :=
  xor (gDifference k₀ R aR) aL

/-- First necessary condition in independent coordinates (R,Z). -/
def middleCondition (k₀ k₁ aL aR bL : Word) (p : State) : Prop :=
  xor (gDifference k₁ p.2 (intermediateDifference k₀ aL aR p.1)) aR = bL

/-- Additional third-round constraint, depending on both coordinates. -/
def finalCondition (k₀ k₁ k₂ aL aR bL bR : Word) (p : State) : Prop :=
  gDifference k₂ (xor (g k₁ p.2) p.1) bL =
    xor bR (intermediateDifference k₀ aL aR p.1)

/-- The coupled condition separates into the middle and final-round tests. -/
theorem coupled_iff_middle_and_final
    (k₀ k₁ k₂ aL aR bL bR : Word) (p : State) :
    threeRoundCoupled k₀ k₁ k₂ aL aR bL bR p.1 p.2 ↔
      middleCondition k₀ k₁ aL aR bL p ∧
        finalCondition k₀ k₁ k₂ aL aR bL bR p := by
  rcases p with ⟨R, Z⟩
  rfl

/-- The candidate set selected without checking the third round. -/
noncomputable def middleCandidates
    (k₀ k₁ aL aR bL : Word) : Finset State := by
  classical
  exact Diffan.FiberDefect.candidates
    (Finset.univ : Finset State) (middleCondition k₀ k₁ aL aR bL)

/-- The candidates rejected by the exact third-round compatibility. -/
noncomputable def couplingDefect
    (k₀ k₁ k₂ aL aR bL bR : Word) : Nat := by
  classical
  exact (Diffan.FiberDefect.rejected
    (Finset.univ : Finset State)
    (middleCondition k₀ k₁ aL aR bL)
    (finalCondition k₀ k₁ k₂ aL aR bL bR)).card

open scoped Classical in
/-- Exact three-round DDT as the count of witnesses passing both tests. -/
private theorem actual_eq_accepted_card
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
      (Diffan.FiberDefect.accepted
        (Finset.univ : Finset State)
        (middleCondition k₀ k₁ aL aR bL)
        (finalCondition k₀ k₁ k₂ aL aR bL bR)).card := by
  classical
  rw [xorDDT_rounds_three]
  unfold threeRoundCoupledCount
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Diffan.FiberDefect.accepted]
  exact coupled_iff_middle_and_final k₀ k₁ k₂ aL aR bL bR p

/-- The rejected witnesses account exactly for the gap in the middle-round upper bound. -/
theorem actual_add_defect_eq_middle
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) +
        couplingDefect k₀ k₁ k₂ aL aR bL bR =
          (middleCandidates k₀ k₁ aL aR bL).card := by
  classical
  have hsplit := Diffan.FiberDefect.card_candidates_eq_accepted_add_rejected
    (Finset.univ : Finset State)
    (middleCondition k₀ k₁ aL aR bL)
    (finalCondition k₀ k₁ k₂ aL aR bL bR)
  rw [← actual_eq_accepted_card k₀ k₁ k₂ aL aR bL bR] at hsplit
  change (middleCandidates k₀ k₁ aL aR bL).card =
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) +
    couplingDefect k₀ k₁ k₂ aL aR bL bR at hsplit
  exact hsplit.symm

/-- The upper candidate count is sharp iff the final-round test accepts
    every candidate satisfying the first two-round condition. -/
theorem actual_eq_middle_iff
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
    (middleCandidates k₀ k₁ aL aR bL).card ↔
    ∀ p : State, middleCondition k₀ k₁ aL aR bL p →
      finalCondition k₀ k₁ k₂ aL aR bL bR p := by
  classical
  rw [actual_eq_accepted_card]
  change
    (Diffan.FiberDefect.accepted
      (Finset.univ : Finset State)
      (middleCondition k₀ k₁ aL aR bL)
      (finalCondition k₀ k₁ k₂ aL aR bL bR)).card =
    (Diffan.FiberDefect.candidates
      (Finset.univ : Finset State)
      (middleCondition k₀ k₁ aL aR bL)).card ↔
    ∀ p : State, middleCondition k₀ k₁ aL aR bL p →
      finalCondition k₀ k₁ k₂ aL aR bL bR p
  simpa only [Finset.mem_univ, true_implies] using
    (Diffan.FiberDefect.card_accepted_eq_candidates_iff
      (Finset.univ : Finset State)
      (middleCondition k₀ k₁ aL aR bL)
      (finalCondition k₀ k₁ k₂ aL aR bL bR))

/-- Dropping the final-round condition gives a rigorous upper bound. -/
theorem actual_le_middle
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) ≤
    (middleCandidates k₀ k₁ aL aR bL).card := by
  have h := actual_add_defect_eq_middle k₀ k₁ k₂ aL aR bL bR
  omega

/-- Equality to the upper bound is equivalent to zero coupling defect. -/
theorem actual_eq_middle_iff_defect_zero
    (k₀ k₁ k₂ aL aR bL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
    (middleCandidates k₀ k₁ aL aR bL).card ↔
    couplingDefect k₀ k₁ k₂ aL aR bL bR = 0 := by
  have h := actual_add_defect_eq_middle k₀ k₁ k₂ aL aR bL bR
  omega

end Magma.DiffanThreeRoundCouplingDefect
