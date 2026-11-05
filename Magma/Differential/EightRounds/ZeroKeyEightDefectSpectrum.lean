module

import all Init.Data.Range.Basic
public import Magma.Differential.EightRounds.ZeroKeyEightDefectWeights
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Complete weighted spectrum of the 76 selected positive-defect pairs

The earlier `ZeroKeyEightDefectWeights` module proves the sharp maximum
of the normalized defect. Here we determine EVERY possible value and
its multiplicity, still only in the certified three-round slice

  (aR, bL, k1) = (1, 0, 0),  odd k0.

The spectrum is computed from the 76 already certified pairs and the
77-entry odd-key reference DDT row. The table is checked by the kernel,
and a uniform
symbolic bridge interprets each value as an actual three-round defect
for EVERY odd first-round key and arbitrary third-round key.

There are 18 distinct nonzero reduced defect values. Every histogram
multiplicity is even. The 76 pairs in fact admit a fixed-point-free
weight-preserving XOR involution, certified on the same finite domain.
-/

namespace Magma.DifanZeroKeyEightDefectSpectrum

open Magma
open Magma.MultiRoundDDT
open Magma.DifanThreeRoundCouplingDefect
open Magma.DifanZeroKeyEightDefectClassification
open Magma.DifanZeroKeyEightDefectWeights

private abbrev Word :=
  V 32

/-- A simultaneous XOR shift of both the left input difference and
    the selected middle difference. The shift is not a key-schedule
    operation: it permutes the zero-key eight-column support. -/
def pairShiftMask : Word := 0x00500000#32

def shiftPair (p : Word × Word) : Word × Word :=
  (xor p.1 pairShiftMask, xor p.2 pairShiftMask)

/-- Applying the shift twice restores the original pair. -/
theorem shiftPair_involutive (p : Word × Word) :
    shiftPair (shiftPair p) = p := by
  rcases p with ⟨aL, bR⟩
  apply Prod.ext
  · change xor (xor aL pairShiftMask) pairShiftMask = aL
    unfold xor
    bv_decide
  · change xor (xor bR pairShiftMask) pairShiftMask = bR
    unfold xor
    bv_decide

/-- The nonzero shift guarantees there are no fixed points. -/
theorem shiftPair_ne_self (p : Word × Word) : shiftPair p ≠ p := by
  intro h
  have hfirst := congrArg (fun q : Word × Word => q.1) h
  change xor p.1 pairShiftMask = p.1 at hfirst
  unfold xor pairShiftMask at hfirst
  bv_decide

/-- The shift permutes the complete set of 76 selected pairs. -/
theorem shiftedPairs_exact :
    positiveDefectPairs.image shiftPair = positiveDefectPairs := by
  decide +kernel

/-- The symmetry preserves each exact reduced defect. Unlike the
    involution law, this finite check depends on the 77-entry DDT row. -/
private theorem shifted_defect_bad_pairs_empty :
    positiveDefectPairs.filter
        (fun p => reducedDefect (shiftPair p).1 (shiftPair p).2 ≠
          reducedDefect p.1 p.2) = ∅ := by
  decide +kernel

theorem shiftPair_preserves_defect (p : Word × Word) (hp : p ∈ positiveDefectPairs) :
    reducedDefect (shiftPair p).1 (shiftPair p).2 = reducedDefect p.1 p.2 := by
  by_contra hn
  have hbad :
    p ∈
      positiveDefectPairs.filter
        (fun q => reducedDefect (shiftPair q).1 (shiftPair q).2 ≠ reducedDefect q.1 q.2) :=
    Finset.mem_filter.mpr ⟨hp, hn⟩
  rw [shifted_defect_bad_pairs_empty] at hbad
  simp at hbad

/- The preceding two-cycle symmetry explains why every multiplicity
   in the finite histogram below is even. -/

/-- The finite 76-pair domain is stable under the involution. -/
theorem shiftPair_mem (p : Word × Word)
    (hp : p ∈ positiveDefectPairs) :
    shiftPair p ∈ positiveDefectPairs := by
  rw [← shiftedPairs_exact]
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- The selected pairs at an exact normalized off-diagonal weight. -/
def defectLevel (n : Nat) : Finset (Word × Word) :=
  positiveDefectPairs.filter (fun p => reducedDefect p.1 p.2 = n)

/-- All distinct normalized defect values present on the 76 selected pairs. -/
def defectValues : Finset Nat :=
  positiveDefectPairs.image (fun p => reducedDefect p.1 p.2)

/-- A generic automatically generated (value, multiplicity) histogram.
    The only Magma-specific part is the input pair set and the weight. -/
def defectSpectrum : Finset (Nat × Nat) :=
  defectValues.image (fun n => (n, (defectLevel n).card))

/-- The complete weighted spectrum. All entries count PAIRS (aL,bR). -/
def expectedSpectrum : Finset (Nat × Nat) :=
  {(131072, 2),
   (2097152, 2),
   (2228224, 2),
   (4194304, 4),
   (4325376, 6),
   (6291456, 10),
   (8388608, 12),
   (10485760, 6),
   (12582912, 4),
   (14811136, 8),
   (16908288, 2),
   (18874368, 2),
   (33554432, 2),
   (35651584, 4),
   (37748736, 2),
   (39845888, 4),
   (41943040, 2),
   (44040192, 2)}

/-- The histogram of the 76 selected pairs agrees with the explicit spectrum. -/
theorem defectSpectrum_exact : defectSpectrum = expectedSpectrum := by
  decide +kernel

/-- The spectrum really has 18 distinct exact defect values. -/
theorem defectSpectrum_card : defectSpectrum.card = 18 := by
  rw [defectSpectrum_exact]
  decide

/-- The histogram covers 76 selected pairs, with no missing mass. -/
theorem spectrum_multiplicity_total :
    (∑ p ∈ expectedSpectrum, p.2) = 76 := by
  decide

/-- The first weighted moment (sum of all reduced defects). -/
theorem spectrum_weighted_total :
    (∑ p ∈ expectedSpectrum, p.1 * p.2) = 1135083520 := by
  decide

/-- Independently certify the first moment directly on the 76 pairs.
    This also guards against a mismatch in histogram bookkeeping. -/
theorem defect_total_exact :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) =
      1135083520 := by
  decide +kernel

/-- Total selected coefficient mass on the SAME 76 pairs. -/
theorem selected_total_exact :
    (∑ p ∈ positiveDefectPairs, reducedSelected p.1 p.2) =
      500170752 := by
  decide +kernel

/-- A global conservation identity. This is symbolic: it follows from
    `reduced_mass_split`, without an independent large computation. -/
theorem global_reduced_mass_split :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) +
      (∑ p ∈ positiveDefectPairs, reducedSelected p.1 p.2) =
        ∑ p ∈ positiveDefectPairs, reducedMass p.1 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact reduced_mass_split p.1 p.2

/-- Summing the full normalized mass with no additional DDT evaluation. -/
theorem total_reduced_mass_exact :
    (∑ p ∈ positiveDefectPairs, reducedMass p.1) =
      1635254272 := by
  have h := global_reduced_mass_split
  rw [defect_total_exact, selected_total_exact] at h
  omega

/-- For ANY odd first-round key, and ANY third key, equality to a
    given exact defect value is equivalent to membership in its
    automatically computed finite level. -/
theorem odd_actual_defect_level_iff
    (k₀ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 1)
    (hp : (aL, bR) ∈ positiveDefectPairs) (n : Nat) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR =
        2 ^ 29 * n ↔
      (aL, bR) ∈ defectLevel n := by
  rw [odd_defect_exact k₀ k₂ aL bR hk]
  constructor
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨hp, ?_⟩
    norm_num at h
    omega
  · intro h
    exact congrArg (fun t : Nat => 2 ^ 29 * t)
      (Finset.mem_filter.mp h).2

/-- The involution preserves the ACTUAL defect for every odd first key
    and every third key, not merely the normalized reference number. -/
theorem odd_actual_defect_shift (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hp : (aL, bR) ∈ positiveDefectPairs) :
    couplingDefect k₀ (0#32) k₂
        (xor aL pairShiftMask) (1#32) (0#32) (xor bR pairShiftMask) =
      couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR := by
  rw [odd_defect_exact k₀ k₂ (xor aL pairShiftMask)
        (xor bR pairShiftMask) hk,
      odd_defect_exact k₀ k₂ aL bR hk]
  have hs := shiftPair_preserves_defect (aL, bR) hp
  change reducedDefect (xor aL pairShiftMask)
      (xor bR pairShiftMask) = reducedDefect aL bR at hs
  exact congrArg (fun n : Nat => 2 ^ 29 * n) hs

/-- At every odd k0, the sum of the *actual*, unnormalized defects
    over the 76 pairs is the finite constant times the exact 2^29
    second-round column weight. -/
theorem odd_actual_defect_total (k₀ k₂ : Word)
    (hk : k₀.toNat % 2 = 1) :
    (∑ p ∈ positiveDefectPairs,
        couplingDefect k₀ (0#32) k₂ p.1 (1#32) (0#32) p.2) =
      2 ^ 29 * 1135083520 := by
  calc
    _ = ∑ p ∈ positiveDefectPairs,
          2 ^ 29 * reducedDefect p.1 p.2 := by
            apply Finset.sum_congr rfl
            intro p _
            exact odd_defect_exact k₀ k₂ p.1 p.2 hk
    _ = 2 ^ 29 * 1135083520 := by
      rw [← Finset.mul_sum, defect_total_exact]

/-- The true three-round selected-coefficient total on the same
    76 pairs is also independent of the particular odd k0 and k2. -/
theorem odd_actual_selected_total (k₀ k₂ : Word)
    (hk : k₀.toNat % 2 = 1) :
    (∑ p ∈ positiveDefectPairs,
        xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
          (p.1, 1#32) (0#32, p.2)) =
      2 ^ 29 * 500170752 := by
  calc
    _ = ∑ p ∈ positiveDefectPairs,
          2 ^ 29 * reducedSelected p.1 p.2 := by
            apply Finset.sum_congr rfl
            intro p _
            exact odd_selected_exact k₀ k₂ p.1 p.2 hk
    _ = 2 ^ 29 * 500170752 := by
      rw [← Finset.mul_sum, selected_total_exact]

end Magma.DifanZeroKeyEightDefectSpectrum
