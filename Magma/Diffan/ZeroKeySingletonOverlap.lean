module

import all Init.Data.Range.Basic
public import Magma.Diffan.EvenUnitOverlapEight

@[expose] public section

/-!
# Singleton support overlaps at zero first and middle keys

For k₀ = k₁ = 0 and aR = 1, the 64 pairs in `predictedPairs` each give
a singleton shifted-row/column support intersection:

  supportOverlap 0 0 aL 1 = {bR}.

The left differences in the list are pairwise distinct, so the complete
support classification determines a unique intermediate difference for
every listed left difference. The convolution mass is 2^58, concentrated
at this intermediate difference. Its coupling defect is zero at the
corresponding output and 2^58 at every other output, for any third key.
-/

namespace Magma.DiffanZeroKeySingletonOverlap

open Magma
open Magma.MultiRoundDDT
open Magma.ZeroLeftSupport
open Magma.ZeroLeft64Exact
open Magma.ZeroLeft64Completeness
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- Check that each left difference in the finite support table selects
    a unique right difference. -/
private def checkUniqueLeft : Bool :=
  predictedPairs.all fun p =>
    predictedPairs.all fun q =>
      decide (p.1 = q.1 → p.2 = q.2)

/-- The 64-pair support table has a unique right difference per left difference. -/
private theorem checkUniqueLeft_true : checkUniqueLeft = true := by
  decide +kernel

/-- In the 64-element certified list, the first coordinate uniquely
    determines the second. This is stronger than `predictedPairs_nodup`. -/
theorem predictedPairs_unique_right (p q : Word × Word)
    (hp : p ∈ predictedPairs) (hq : q ∈ predictedPairs)
    (hleft : p.1 = q.1) : p.2 = q.2 := by
  have hcheck :
      predictedPairs.all (fun p =>
        predictedPairs.all (fun q =>
          decide (p.1 = q.1 → p.2 = q.2))) = true :=
    checkUniqueLeft_true
  have hp' := (List.all_eq_true.mp hcheck) p hp
  have hq' := (List.all_eq_true.mp hp') q hq
  exact (of_decide_eq_true hq') hleft

/-- The support overlap is exactly the fiber of the certified pair list
    over the selected left difference. -/
theorem zeroKey_overlap_mem_iff_listed (aL c : Word) :
    c ∈ supportOverlap (0#32) (0#32) aL (1#32) ↔
      (aL, c) ∈ predictedPairs := by
  calc
    c ∈ supportOverlap (0#32) (0#32) aL (1#32) ↔
        0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) (0#32))
          (aL, 1#32) (0#32, c) :=
      (zeroLeftDDT_pos_iff_mem (0#32) (0#32) (0#32)
        aL (1#32) c).symm
    _ ↔ (aL, c) ∈ predictedPairs :=
      zeroLeftSlice_possible_iff_listed (0#32) aL c

/-- The overlap can contain at most one intermediate difference for any
    fixed aL, independently of a requested output bR. -/
theorem zeroKey_overlap_unique (aL c d : Word)
    (hc : c ∈ supportOverlap (0#32) (0#32) aL (1#32))
    (hd : d ∈ supportOverlap (0#32) (0#32) aL (1#32)) :
    c = d := by
  apply predictedPairs_unique_right (aL, c) (aL, d)
    ((zeroKey_overlap_mem_iff_listed aL c).mp hc)
    ((zeroKey_overlap_mem_iff_listed aL d).mp hd)
  rfl

/-- Each listed left difference has a singleton support overlap, whose
    element is the corresponding right difference. -/
theorem zeroKey_singleton_of_listed (aL chosen : Word)
    (hp : (aL, chosen) ∈ predictedPairs) :
    supportOverlap (0#32) (0#32) aL (1#32) =
      ({chosen} : Set Word) := by
  have hchosen : chosen ∈ supportOverlap (0#32) (0#32) aL (1#32) :=
    (zeroKey_overlap_mem_iff_listed aL chosen).mpr hp
  apply Set.Subset.antisymm
  · intro c hc
    exact Set.mem_singleton_iff.mpr
      (zeroKey_overlap_unique aL c chosen hc hchosen)
  · intro c hc
    have heq : c = chosen := Set.mem_singleton_iff.mp hc
    subst c
    exact hchosen

/-- All listed pairs have a zero coupling defect for every last key. -/
theorem zeroKey_defect_zero_of_listed (k₂ aL chosen : Word)
    (hp : (aL, chosen) ∈ predictedPairs) :
    couplingDefect (0#32) (0#32) k₂ aL (1#32) (0#32) chosen = 0 := by
  apply (couplingDefect_zero_iff_subset
    (0#32) (0#32) k₂ aL (1#32) chosen).mpr
  rw [zeroKey_singleton_of_listed aL chosen hp]

/-- The unique contributing convolution term is exactly 2^58. -/
theorem zeroKey_overlapWeight_exact_of_listed (aL chosen : Word)
    (hp : (aL, chosen) ∈ predictedPairs) :
    overlapWeight (0#32) (0#32) aL (1#32) chosen = 2 ^ 58 := by
  have h := predictedPairs_exact_count (0#32) aL chosen hp
  rw [xorDDT_rounds_three_zero_left_factorization] at h
  change overlapWeight (0#32) (0#32) aL (1#32) chosen = 2 ^ 58 at h
  exact h

/-- All other intermediate differences have zero convolution weight. -/
theorem zeroKey_overlapWeight_other_zero (aL chosen c : Word)
    (hp : (aL, chosen) ∈ predictedPairs) (hne : c ≠ chosen) :
    overlapWeight (0#32) (0#32) aL (1#32) c = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  have hc := (overlapWeight_pos_iff (0#32) (0#32) aL (1#32) c).mp hpos
  have hmem : c ∈ ({chosen} : Set Word) := by
    rw [← zeroKey_singleton_of_listed aL chosen hp]
    exact hc
  exact hne (Set.mem_singleton_iff.mp hmem)

/-- At every listed left difference aL,
    all convolution mass 2^58 is concentrated at a unique chosen word.
    The coupling defect is zero exactly at that output, and 2^58 at
    every other requested output, independently of the third key. -/
theorem zeroKey_defect_exact_of_listed
    (k₂ aL chosen requested : Word)
    (hp : (aL, chosen) ∈ predictedPairs) :
    couplingDefect (0#32) (0#32) k₂ aL (1#32) (0#32) requested =
      if requested = chosen then 0 else 2 ^ 58 := by
  classical
  by_cases heq : requested = chosen
  · subst requested
    simp only [ite_true]
    exact zeroKey_defect_zero_of_listed k₂ aL chosen hp
  · simp only [heq, ite_false]
    have hmem : chosen ∈ (Finset.univ : Finset Word).erase requested :=
      Finset.mem_erase.mpr ⟨Ne.symm heq, Finset.mem_univ chosen⟩
    have hsum :
        offDiagonalMass (0#32) (0#32) aL (1#32) requested =
          overlapWeight (0#32) (0#32) aL (1#32) chosen := by
      unfold offDiagonalMass
      exact Finset.sum_eq_single_of_mem chosen hmem
        (fun c _ hne => zeroKey_overlapWeight_other_zero aL chosen c hp hne)
    calc
      couplingDefect (0#32) (0#32) k₂ aL (1#32) (0#32) requested =
          offDiagonalMass (0#32) (0#32) aL (1#32) requested :=
        couplingDefect_eq_offDiagonalMass
          (0#32) (0#32) k₂ aL (1#32) requested
      _ = overlapWeight (0#32) (0#32) aL (1#32) chosen := hsum
      _ = 2 ^ 58 := zeroKey_overlapWeight_exact_of_listed aL chosen hp

/-- Each certified member is simultaneously a strictly positive exact
    DDT coefficient and a zero-defect characteristic. -/
theorem zeroKey_positive_zeroDefect_of_listed
    (k₂ aL bR : Word) (hp : (aL,bR) ∈ predictedPairs) :
    couplingDefect (0#32) (0#32) k₂ aL (1#32) (0#32) bR = 0 ∧
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) = 2 ^ 58 := by
  exact ⟨zeroKey_defect_zero_of_listed k₂ aL bR hp,
    predictedPairs_exact_count k₂ aL bR hp⟩

/-- Conversely, every positive entry on this slice comes from the
    existing 64-member list; thus this family is COMPLETE. -/
theorem zeroKey_positive_zeroDefect_iff_listed
    (k₂ aL bR : Word) :
    (couplingDefect (0#32) (0#32) k₂ aL (1#32) (0#32) bR = 0 ∧
      0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
        (aL, 1#32) (0#32, bR)) ↔
      (aL,bR) ∈ predictedPairs := by
  constructor
  · intro h
    exact (zeroLeftSlice_possible_iff_listed k₂ aL bR).mp h.2
  · intro hp
    obtain ⟨hd, hw⟩ := zeroKey_positive_zeroDefect_of_listed k₂ aL bR hp
    exact ⟨hd, by rw [hw]; norm_num⟩

/-- Concrete nontrivial instance: 0x00301000 -> 0x00300000 belongs to
    the already certified 64-pair family, and works for EVERY third key. -/
theorem concrete_singleton_example (k₂ : Word) :
    supportOverlap (0#32) (0#32) (0x00301000#32) (1#32) =
      ({0x00300000#32} : Set Word) ∧
    couplingDefect (0#32) (0#32) k₂
      (0x00301000#32) (1#32) (0#32) (0x00300000#32) = 0 ∧
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (0x00301000#32, 1#32) (0#32, 0x00300000#32) = 2 ^ 58 := by
  have hp : ((0x00301000#32), (0x00300000#32)) ∈ predictedPairs := by
    decide
  exact ⟨zeroKey_singleton_of_listed _ _ hp,
    zeroKey_positive_zeroDefect_of_listed k₂ _ _ hp⟩

/-- Moving the desired output away from the only supported word turns
    the entire 2^58 convolution mass into an off-diagonal defect. -/
theorem concrete_offDiagonal_defect (k₂ : Word) :
    couplingDefect (0#32) (0#32) k₂
      (0x00301000#32) (1#32) (0#32) (0x00400000#32) = 2 ^ 58 := by
  have hp : ((0x00301000#32), (0x00300000#32)) ∈ predictedPairs := by
    decide
  have h := zeroKey_defect_exact_of_listed k₂
    (0x00301000#32) (0x00300000#32) (0x00400000#32) hp
  have hne : (0x00400000#32) ≠ (0x00300000#32) := by decide
  simpa only [hne, ite_false] using h

end Magma.DiffanZeroKeySingletonOverlap
