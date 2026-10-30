module

import all Init.Data.Range.Basic
public import Magma.Diffan.ZeroKeyEightDefectClassification

@[expose] public section

/-!
# The exact weighted defect over all 76 selected positive-defect pairs

Work in the previously certified slice (aR, bL, k1) = (1, 0, 0).
The 76 pairs (aL, bR) with positive chosen coefficient and positive
coupling defect are exactly `positiveDefectPairs`. For any odd k0,
all genuine first-round coefficients are the same 77-entry table
`OddUnitInput77.oddReferenceCount`.

The multiplicity of the overlap does NOT determine the numerical defect:
the largest reduced defect among the 76 pairs is 44,040,192, reached
at exactly two pairs, each having FOUR surviving differences (rather
than the maximum multiplicity SIX). The full actual defect equals the
reduced integer multiplied by 2^29, the exact second-round column weight.

The finite certificates inspect the certified 24-by-eight candidate table.
-/

namespace Magma.DiffanZeroKeyEightDefectWeights

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanZeroLeftSupportOverlap
open Magma.OddUnitInput77
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanZeroKeyEightColumn
open Magma.DiffanZeroKeyEightMultiplicity
open Magma.DiffanZeroKeyEightDefectClassification
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

/-- Remove the universal weight 2^29 from the off-diagonal convolution.
    This is an eight-element lookup into the already certified odd DDT row. -/
def reducedDefect (aL bR : Word) : Nat :=
  ∑ c ∈ zeroColumnSupport.erase bR, oddReferenceCount (xor c aL)

/-- The complete compatible mass, in the same normalization. -/
def reducedMass (aL : Word) : Nat :=
  ∑ c ∈ zeroColumnSupport, oddReferenceCount (xor c aL)

/-- A selected diagonal entry, in normalized odd-first-key units. -/
def reducedSelected (aL bR : Word) : Nat :=
  if bR ∈ zeroColumnSupport then oddReferenceCount (xor bR aL) else 0

/-- Exact off-diagonal defect at any output bR, not just at a selected
    positive coefficient. Uniform for every odd k0 and every k2. -/
theorem odd_defect_exact (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR =
      2 ^ 29 * reducedDefect aL bR := by
  rw [couplingDefect_eight_parity]
  have hne : ¬ k₀.toNat % 2 = 0 := by omega
  simp only [parityRowCount, hne, ite_false]
  change (∑ c ∈ zeroColumnSupport.erase bR,
      2 ^ 29 * oddReferenceCount (xor c aL)) =
    2 ^ 29 * (∑ c ∈ zeroColumnSupport.erase bR,
      oddReferenceCount (xor c aL))
  rw [Finset.mul_sum]

/-- Exact convolution, after dropping the common second-round factor. -/
theorem odd_convolution_exact (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    (∑ c : Word, overlapWeight k₀ (0#32) aL (1#32) c) =
      2 ^ 29 * reducedMass aL := by
  rw [fullConvolution_eight_parity]
  have hne : ¬ k₀.toNat % 2 = 0 := by omega
  simp only [parityRowCount, hne, ite_false]
  change (∑ c ∈ zeroColumnSupport,
      2 ^ 29 * oddReferenceCount (xor c aL)) =
    2 ^ 29 * (∑ c ∈ zeroColumnSupport,
      oddReferenceCount (xor c aL))
  rw [Finset.mul_sum]

/-- Numerical decomposition of the full normalized mass into one
    selected contribution and all others, including unsupported bR. -/
theorem reduced_mass_split (aL bR : Word) :
    reducedDefect aL bR + reducedSelected aL bR =
      reducedMass aL := by
  classical
  by_cases hc : bR ∈ zeroColumnSupport
  · simp only [reducedDefect, reducedSelected, reducedMass, ite_eq_left hc]
    exact Finset.sum_erase_add zeroColumnSupport
      (fun c => oddReferenceCount (xor c aL)) hc
  · have he : zeroColumnSupport.erase bR = zeroColumnSupport :=
      Finset.erase_eq_of_notMem hc
    simp only [reducedDefect, reducedSelected, reducedMass, he, ite_eq_right hc,
      Nat.add_zero]

/-- Multiplying this decomposition by 2^29 recovers the actual
    three-round selected coefficient plus the exact off-diagonal defect. -/
theorem odd_selected_exact (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) =
      2 ^ 29 * reducedSelected aL bR := by
  rw [threeRound_zeroLeft_eight]
  by_cases hc : bR ∈ zeroColumnSupport
  · rw [ite_eq_left hc, odd_key_complete_DDT k₀ (xor bR aL) hk]
    simp only [reducedSelected, ite_eq_left hc]
  · rw [ite_eq_right hc]
    simp only [reducedSelected, ite_eq_right hc, Nat.mul_zero]

/-- A fully quantified conservation formula for the symbolic
    convolution mass, valid at ALL outputs including zero coefficients. -/
theorem odd_defect_plus_selected (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR +
      xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) =
      2 ^ 29 * reducedMass aL := by
  rw [odd_defect_exact k₀ k₂ aL bR hk,
    odd_selected_exact k₀ k₂ aL bR hk,
    ← Nat.mul_add, reduced_mass_split]

/-- The reduced defect is at most 44,040,192 on all 76 selected pairs. -/
private theorem finite_upper_certificate :
    positiveDefectPairs.filter
        (fun p => 44040192 < reducedDefect p.1 p.2) = ∅ := by
  decide +kernel

private theorem finite_upper_bound (p : Word × Word) (hp : p ∈ positiveDefectPairs) :
    reducedDefect p.1 p.2 ≤ 44040192 := by
  by_contra hn
  have hbad : p ∈ positiveDefectPairs.filter (fun q => 44040192 < reducedDefect q.1 q.2) :=
    Finset.mem_filter.mpr ⟨hp, by omega⟩
  rw [finite_upper_certificate] at hbad
  simp at hbad

/-- Two exact maximizers of the normalized selected defect. -/
def peakPairs : Finset (Word × Word) :=
  positiveDefectPairs.filter
    (fun p => reducedDefect p.1 p.2 = 44040192)

theorem peakPairs_exact :
    peakPairs =
      ({(0x0094E800#32, 0x00C00000#32),
          (0x00C4E800#32, 0x00900000#32)} :
        Finset (Word × Word)) := by
  decide +kernel

theorem peakPairs_card : peakPairs.card = 2 := by
  rw [peakPairs_exact]
  decide

/-- At an odd first key, 44,040,192 * 2^29 is the SHARP largest
    defect among all 76 pairs with a positive selected coefficient. -/
theorem odd_selected_defect_upper (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hp : (aL, bR) ∈ positiveDefectPairs) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR ≤
      2 ^ 29 * 44040192 := by
  rw [odd_defect_exact k₀ k₂ aL bR hk]
  exact Nat.mul_le_mul_left (2 ^ 29)
    (finite_upper_bound (aL, bR) hp)

/-- The numerical maximizers are EXACTLY the two tabulated pairs,
    independently of the particular odd k0 and the third key k2. -/
theorem odd_selected_peak_iff (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hp : (aL, bR) ∈ positiveDefectPairs) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR =
      2 ^ 29 * 44040192 ↔ (aL, bR) ∈ peakPairs := by
  rw [odd_defect_exact k₀ k₂ aL bR hk]
  constructor
  · intro h
    have he : reducedDefect aL bR = 44040192 := by
      norm_num at h
      omega
    exact Finset.mem_filter.mpr ⟨hp, he⟩
  · intro h
    exact congrArg (fun n : Nat => 2 ^ 29 * n)
      (Finset.mem_filter.mp h).2

/-- Unlike the overlap cardinality, the maximum weighted defect
    occurs at input differences with FOUR surviving intermediates. -/
theorem peak_inputs_have_four_survivors :
    (oddSurvivors (0x0094E800#32)).card = 4 ∧
      (oddSurvivors (0x00C4E800#32)).card = 4 := by
  constructor <;> decide +kernel

/-- Two established sixfold witnesses have a much smaller maximum
    normalized defect (18,874,368 versus 44,040,192). -/
theorem sixfold_witness_weight_comparison :
    (oddSurvivors (0x00ECE800#32)).card = 6 ∧
    (oddSurvivors (0x00BCE800#32)).card = 6 ∧
    reducedDefect (0x00ECE800#32) (0x00300000#32) = 18874368 ∧
    reducedDefect (0x00BCE800#32) (0x00600000#32) = 18874368 ∧
    18874368 < 44040192 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · norm_num

end Magma.DiffanZeroKeyEightDefectWeights
