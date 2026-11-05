module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundConvolutionDefect

@[expose] public section

/-!
# Zero-left three-round defect as a support intersection

For bL = 0 the exact three-round differential coefficient is the c = bR
term of the two-round-function DDT convolution. The coupling defect is
exactly the sum of its other terms. Since the summands are natural numbers,
the defect vanishes precisely when the shifted k0 row and the k1 column
have no common support outside c = bR.

The support intersection is represented as a set; its containment in a
singleton characterizes zero defect, while equality characterizes zero
defect with a positive differential coefficient.
-/

namespace Magma.DifanZeroLeftSupportOverlap

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanThreeRoundConvolutionDefect
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- The c-th candidate in the two-function DDT convolution, with bL=0.
    The first factor is a shifted ROW; the second is a COLUMN. -/
def overlapWeight (k₀ k₁ aL aR c : Word) : Nat :=
  xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR

/-- Actual intersection of the shifted first-round row support with
    the second-round column support; no confusion with two DDT rows. -/
def supportOverlap (k₀ k₁ aL aR : Word) : Set Word :=
  {c | 0 < xorDDT_g k₀ aR (xor c aL) ∧ 0 < xorDDT_g k₁ c aR}

/-- All convolution mass *except* the c = bR term. -/
def offDiagonalMass (k₀ k₁ aL aR bR : Word) : Nat :=
  ∑ c ∈ (Finset.univ : Finset Word).erase bR,
    overlapWeight k₀ k₁ aL aR c

/-- One weighted term is positive exactly on the support intersection. -/
theorem overlapWeight_pos_iff (k₀ k₁ aL aR c : Word) :
    0 < overlapWeight k₀ k₁ aL aR c ↔
      c ∈ supportOverlap k₀ k₁ aL aR := by
  change 0 < xorDDT_g k₀ aR (xor c aL) * xorDDT_g k₁ c aR ↔
    (0 < xorDDT_g k₀ aR (xor c aL) ∧ 0 < xorDDT_g k₁ c aR)
  constructor
  · intro h
    exact ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
  · rintro ⟨h₀, h₁⟩
    exact Nat.mul_pos h₀ h₁

/-- Off-diagonal mass is zero iff every other c has zero weight.
    A zero term means at least one of the two DDT coefficients vanishes. -/
theorem offDiagonalMass_zero_iff
    (k₀ k₁ aL aR bR : Word) :
    offDiagonalMass k₀ k₁ aL aR bR = 0 ↔
      ∀ c : Word, c ≠ bR → c ∉ supportOverlap k₀ k₁ aL aR := by
  unfold offDiagonalMass
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h c hneq hc
    have hz : overlapWeight k₀ k₁ aL aR c = 0 :=
      h c (Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ c⟩)
    have hp := (overlapWeight_pos_iff k₀ k₁ aL aR c).mpr hc
    omega
  · intro h c hc
    have hneq : c ≠ bR := (Finset.mem_erase.mp hc).1
    by_cases hp : 0 < overlapWeight k₀ k₁ aL aR c
    · exact False.elim (h c hneq ((overlapWeight_pos_iff k₀ k₁ aL aR c).mp hp))
    · exact Nat.eq_zero_of_not_pos hp

/-- Zero off-diagonal mass means that only the selected difference can
    belong to both local supports. -/
theorem offDiagonalMass_zero_iff_subset
    (k₀ k₁ aL aR bR : Word) :
    offDiagonalMass k₀ k₁ aL aR bR = 0 ↔
      supportOverlap k₀ k₁ aL aR ⊆ ({bR} : Set Word) := by
  rw [offDiagonalMass_zero_iff]
  constructor
  · intro h c hc
    by_contra hne
    exact h c (by simpa only [Set.mem_singleton_iff] using hne) hc
  · intro h c hne hc
    have hb := h hc
    exact hne (Set.mem_singleton_iff.mp hb)

/-- Positive off-diagonal mass is witnessed by an actual positive
    intersection point c different from the selected bR. -/
theorem offDiagonalMass_pos_iff
    (k₀ k₁ aL aR bR : Word) :
    0 < offDiagonalMass k₀ k₁ aL aR bR ↔
      ∃ c : Word, c ≠ bR ∧ c ∈ supportOverlap k₀ k₁ aL aR := by
  unfold offDiagonalMass
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, (Finset.mem_erase.mp hc).1,
      (overlapWeight_pos_iff k₀ k₁ aL aR c).mp hp⟩
  · rintro ⟨c, hne, hc⟩
    exact ⟨c, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ c⟩,
      (overlapWeight_pos_iff k₀ k₁ aL aR c).mpr hc⟩

/-- For zero left output difference, the coupling defect consists of
    the convolution terms outside the selected intermediate difference. -/
theorem couplingDefect_eq_offDiagonalMass
    (k₀ k₁ k₂ aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      offDiagonalMass k₀ k₁ aL aR bR := by
  let f : Word → Nat := overlapWeight k₀ k₁ aL aR
  have hzero : xor (0#32) aR = aR := by
    change (0#32) ^^^ aR = aR
    exact BitVec.zero_xor
  have hconv := actual_add_defect_eq_convolution
    k₀ k₁ k₂ aL aR (0#32) bR
  rw [xorDDT_rounds_three_zero_left_factorization, hzero] at hconv
  have hcore : f bR + couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      ∑ c : Word, f c := by
    simpa only [f, overlapWeight] using hconv
  have hsplit : offDiagonalMass k₀ k₁ aL aR bR + f bR =
      ∑ c : Word, f c := by
    change (∑ c ∈ (Finset.univ : Finset Word).erase bR, f c) + f bR =
      ∑ c : Word, f c
    exact Finset.sum_erase_add (Finset.univ : Finset Word)
      f (Finset.mem_univ bR)
  omega

/-- For the three-round coupling defect, zero is equivalent
    to the intersection of supports lying inside the single allowed c. -/
theorem couplingDefect_zero_iff_subset
    (k₀ k₁ k₂ aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR = 0 ↔
      supportOverlap k₀ k₁ aL aR ⊆ ({bR} : Set Word) := by
  rw [couplingDefect_eq_offDiagonalMass,
    offDiagonalMass_zero_iff_subset]

/-- A positive coupling defect has a concrete off-diagonal witness.
    In particular, one can search for a support intersection point rather
    than calculate the full numeric defect. -/
theorem couplingDefect_pos_iff_exists_offDiagonal
    (k₀ k₁ k₂ aL aR bR : Word) :
    0 < couplingDefect k₀ k₁ k₂ aL aR (0#32) bR ↔
      ∃ c : Word, c ≠ bR ∧ c ∈ supportOverlap k₀ k₁ aL aR := by
  rw [couplingDefect_eq_offDiagonalMass, offDiagonalMass_pos_iff]

/-- The off-diagonal sum depends only on the first two round keys,
    so the zero-left coupling defect is independent of the third key. -/
theorem couplingDefect_zeroLeft_independent_third_key
    (k₀ k₁ k₂ k₂' aL aR bR : Word) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR =
      couplingDefect k₀ k₁ k₂' aL aR (0#32) bR := by
  rw [couplingDefect_eq_offDiagonalMass,
    couplingDefect_eq_offDiagonalMass]

/-- The actual zero-left DDT entry is positive iff the chosen
    intermediate difference bR belongs to BOTH local supports. -/
theorem zeroLeftDDT_pos_iff_mem
    (k₀ k₁ k₂ aL aR bR : Word) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) ↔
    bR ∈ supportOverlap k₀ k₁ aL aR := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  exact overlapWeight_pos_iff k₀ k₁ aL aR bR

/-- Zero defect and a positive exact differential coefficient hold
    precisely when the support intersection is the singleton {bR}.
    This is stronger than merely being a subset of {bR}. -/
theorem zeroDefect_and_positive_iff_singleton
    (k₀ k₁ k₂ aL aR bR : Word) :
    (couplingDefect k₀ k₁ k₂ aL aR (0#32) bR = 0 ∧
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR)) ↔
      supportOverlap k₀ k₁ aL aR = ({bR} : Set Word) := by
  rw [couplingDefect_zero_iff_subset, zeroLeftDDT_pos_iff_mem]
  constructor
  · rintro ⟨hsubset, hb⟩
    apply Set.Subset.antisymm hsubset
    intro c hc
    have heq : c = bR := Set.mem_singleton_iff.mp hc
    subst c
    exact hb
  · intro h
    constructor
    · rw [h]
    · rw [h]
      exact Set.mem_singleton bR

/-- If the two local supports are disjoint, there is zero coupling
    defect BUT ALSO no positive 3-round coefficient on this slice. -/
theorem disjoint_support_gives_zero_defect_and_zero_ddt
    (k₀ k₁ k₂ aL aR bR : Word)
    (h : supportOverlap k₀ k₁ aL aR = ∅) :
    couplingDefect k₀ k₁ k₂ aL aR (0#32) bR = 0 ∧
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (0#32, bR) = 0 := by
  constructor
  · apply (couplingDefect_zero_iff_subset k₀ k₁ k₂ aL aR bR).mpr
    rw [h]
    exact Set.empty_subset _
  · apply Nat.eq_zero_of_not_pos
    intro hp
    have hb := (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL aR bR).mp hp
    rw [h] at hb
    exact hb

end Magma.DifanZeroLeftSupportOverlap
