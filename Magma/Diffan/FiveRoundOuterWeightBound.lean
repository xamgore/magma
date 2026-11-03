module
import all Init.Data.Range.Basic
public import Magma.Diffan.OneHotFourHotPositive

@[expose] public section

/-!
# A sharp weight-sum conjecture for five ordinary Magma rounds

This concerns *outer* five-round differences (alpha,0) -> (0,sigma)
and counts the active bits in the 32-bit nonzero halves. The formal
lower bound is OPEN; the equality case is proved by a real trajectory.

The theorem below reduces the lower bound to four families of
impossible differential claims; two more follow by Feistel reversal.
No solver-generated UNSAT results are assumed as axioms.
-/

namespace Magma.DiffanFiveRoundOuterWeightBound

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFiveRoundDDTReverse
open Magma.DiffanOneHotFourHotPositive

private abbrev Word :=
  V 32

/-- Hamming weight of a 32-bit difference. -/
def wt (a : Word) : Nat := a.cpop.toNat

/-- A generic full fixed-key forbidden weight class. -/
def WeightClassImpossible (wa ws : Nat) : Prop :=
  ∀ k₀ k₁ k₂ k₃ k₄ a s : Word,
    wt a = wa → wt s = ws →
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0

/-- The main conjecture: nonzero outer differences cannot occur
    with fewer than five active bits across their two halves. -/
def OuterWeightLowerBoundFive : Prop :=
  ∀ k₀ k₁ k₂ k₃ k₄ a s : Word,
    0 < wt a → 0 < wt s →
    0 < xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) →
    5 ≤ wt a + wt s

/-- Feistel reversal converts any weight class to its transposed class. -/
theorem weightClass_reverse (wa ws : Nat)
    (h : WeightClassImpossible wa ws) :
    WeightClassImpossible ws wa := by
  intro k₀ k₁ k₂ k₃ k₄ a s ha hs
  rw [outer_ddt_reverse]
  exact h k₄ k₃ k₂ k₁ k₀ s a hs ha

/-- Four ordinary weight classes suffice for the full lower bound:
    (1,1), (1,2), (1,3), (2,2). The (2,1) and (3,1) classes are
    their proven Feistel reversals. -/
theorem outer_lower_bound_of_four_classes
    (h11 : WeightClassImpossible 1 1)
    (h12 : WeightClassImpossible 1 2)
    (h13 : WeightClassImpossible 1 3)
    (h22 : WeightClassImpossible 2 2) :
    OuterWeightLowerBoundFive := by
  intro k₀ k₁ k₂ k₃ k₄ a s ha hs hpos
  by_contra hnot
  have hsmall : wt a + wt s < 5 := by omega
  have hcases :
      (wt a = 1 ∧ wt s = 1) ∨
      (wt a = 1 ∧ wt s = 2) ∨
      (wt a = 1 ∧ wt s = 3) ∨
      (wt a = 2 ∧ wt s = 1) ∨
      (wt a = 2 ∧ wt s = 2) ∨
      (wt a = 3 ∧ wt s = 1) := by omega
  have hz : xorDDT_rounds 5
      (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) (a, 0#32) (0#32, s) = 0 := by
    rcases hcases with h | h | h | h | h | h
    · exact h11 k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
    · exact h12 k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
    · exact h13 k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
    · exact (weightClass_reverse 1 2 h12) k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
    · exact h22 k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
    · exact (weightClass_reverse 1 3 h13) k₀ k₁ k₂ k₃ k₄ a s h.1 h.2
  omega

theorem weightClass_of_outer_lower_bound (h : OuterWeightLowerBoundFive) (wa ws : Nat) (ha : 0 < wa)
    (hs : 0 < ws) (hsmall : wa + ws < 5) : WeightClassImpossible wa ws := by
  intro k₀ k₁ k₂ k₃ k₄ a s haw hsw
  by_contra hzero
  have hpos : 0 < xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) (a, 0#32) (0#32, s) := by omega
  have hbound := h k₀ k₁ k₂ k₃ k₄ a s (by omega) (by omega) hpos
  omega

/-- A precise reduction of the unproved universal bound to four
    independent forbidden weight classes (the other two reverse). -/
theorem lowerBound_iff_four_classes :
    OuterWeightLowerBoundFive ↔
      WeightClassImpossible 1 1 ∧
      WeightClassImpossible 1 2 ∧
      WeightClassImpossible 1 3 ∧
      WeightClassImpossible 2 2 := by
  constructor
  · intro h
    exact ⟨weightClass_of_outer_lower_bound h 1 1 (by omega) (by omega) (by omega),
      weightClass_of_outer_lower_bound h 1 2 (by omega) (by omega) (by omega),
      weightClass_of_outer_lower_bound h 1 3 (by omega) (by omega) (by omega),
      weightClass_of_outer_lower_bound h 2 2 (by omega) (by omega) (by omega)⟩
  · rintro ⟨h11, h12, h13, h22⟩
    exact outer_lower_bound_of_four_classes h11 h12 h13 h22

/-- The bound five is ATTAINED at a real kernel-checked trajectory:
    alpha = 0x00000080, sigma = 0xc0000820. -/
theorem weight_sum_five_attainable :
    ∃ k₀ k₁ k₂ k₃ k₄ a s : Word,
      wt a + wt s = 5 ∧
      0 < xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, s) := by
  refine ⟨0#32, 0x00002056#32, 0xfdfa7789#32,
    0xf0f8d960#32, 0#32, 0x00000080#32, 0xc0000820#32,
    ?_, ?_⟩
  · decide +kernel
  · exact positive_oneHot_to_fourHot

end Magma.DiffanFiveRoundOuterWeightBound
