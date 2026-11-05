module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.ZeroLeftSupportOverlap
public import Magma.DDT.ZeroLeft.ParityCompleteSlice

@[expose] public section

/-!
# Eight-candidate overlap criterion for even first keys

For aR = 1 and an even first round key, the complete output support of
its one-round differential is the certified eight-element `eightOffsets`.
The middle-difference overlap of the zero-left three-round slice can
therefore be decided using eight second-key DDT column entries.

The two distinct conclusions must not be confused:
* zero off-diagonal defect: all candidates except bR have zero column mass;
* zero defect AND positive three-round DDT: in addition, the bR candidate
  exists and has positive column mass.

The criteria apply to each choice of the second key and the differences
aL and bR.
-/

namespace Magma.DifanEvenUnitOverlapEight

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- XORing twice by the same word restores the initial 32-bit word. -/
private theorem xor_xor_cancel (x a : Word) :
    xor (xor x a) a = x := by
  change (x ^^^ a) ^^^ a = x
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The eight candidate intermediate differences after the shift by aL. -/
def eightCandidates (aL : Word) : Finset Word :=
  eightOffsets.image (fun d => xor d aL)

/-- An XOR shift is injective, so the candidate set still has eight words. -/
private theorem xor_shift_injective (a : Word) :
    Function.Injective (fun d : Word => xor d a) := by
  intro x y h
  have hh := congrArg (fun d : Word => xor d a) h
  simpa only [xor_xor_cancel] using hh

/-- Candidate membership is the same as membership in the shifted row. -/
theorem mem_eightCandidates_iff (aL c : Word) :
    c ∈ eightCandidates aL ↔ xor c aL ∈ eightOffsets := by
  unfold eightCandidates
  constructor
  · intro hc
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hc
    have hh : xor c aL = d := by
      rw [← hdc]
      exact xor_xor_cancel d aL
    rw [hh]
    exact hd
  · intro hc
    apply Finset.mem_image.mpr
    refine ⟨xor c aL, hc, ?_⟩
    exact xor_xor_cancel c aL

/-- Each XOR shift preserves the eight-element candidate set size. -/
theorem eightCandidates_card (aL : Word) :
    (eightCandidates aL).card = 8 := by
  unfold eightCandidates
  rw [Finset.card_image_of_injective _ (xor_shift_injective aL)]
  exact eightOffsets_card

/-- For an even k0 the first DDT coefficient is completely explicit. -/
theorem even_first_factor (k₀ aL c : Word)
    (hk : k₀.toNat % 2 = 0) :
    xorDDT_g k₀ (1#32) (xor c aL) =
      if xor c aL ∈ eightOffsets then 2 ^ 29 else 0 := by
  rw [one_round_unit_exact]
  simp only [parityRowCount, hk, ite_true]

/-- For even k0, the entire overlap is supported inside the eight
    shifted offsets and is filtered only by the second DDT column. -/
theorem even_overlap_mem_iff (k₀ k₁ aL c : Word)
    (hk : k₀.toNat % 2 = 0) :
    c ∈ supportOverlap k₀ k₁ aL (1#32) ↔
      c ∈ eightCandidates aL ∧ 0 < xorDDT_g k₁ c (1#32) := by
  have hrow :
      (0 < xorDDT_g k₀ (1#32) (xor c aL)) ↔
        xor c aL ∈ eightOffsets := by
    rw [even_first_factor k₀ aL c hk]
    by_cases hm : xor c aL ∈ eightOffsets
    · simp [hm]
    · simp [hm]
  change (0 < xorDDT_g k₀ (1#32) (xor c aL) ∧
      0 < xorDDT_g k₁ c (1#32)) ↔ _
  rw [hrow, mem_eightCandidates_iff]

/-- In this slice, no intermediate difference outside the eight candidates
    can belong to the intersection of local DDT supports. -/
theorem even_overlap_subset_candidates
    (k₀ k₁ aL : Word) (hk : k₀.toNat % 2 = 0) :
    ∀ c : Word, c ∈ supportOverlap k₀ k₁ aL (1#32) →
      c ∈ eightCandidates aL := by
  intro c hc
  exact ((even_overlap_mem_iff k₀ k₁ aL c hk).mp hc).1

/-- Exact finite criterion for vanishing three-round coupling defect.
    Only eight local column coefficients remain to be checked. -/
theorem even_defect_zero_iff_eight_tests
    (k₀ k₁ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR = 0 ↔
      ∀ d ∈ eightOffsets, xor d aL ≠ bR →
        xorDDT_g k₁ (xor d aL) (1#32) = 0 := by
  rw [couplingDefect_zero_iff_subset]
  constructor
  · intro hs d hd hne
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hc : xor d aL ∈ supportOverlap k₀ k₁ aL (1#32) :=
      (even_overlap_mem_iff k₀ k₁ aL (xor d aL) hk).mpr
        ⟨(mem_eightCandidates_iff aL (xor d aL)).mpr
            (by simpa only [xor_xor_cancel] using hd), hp⟩
    exact hne (Set.mem_singleton_iff.mp (hs hc))
  · intro ht c hc
    have hpair := (even_overlap_mem_iff k₀ k₁ aL c hk).mp hc
    by_contra hne
    have hneq : c ≠ bR := by
      simpa only [Set.mem_singleton_iff] using hne
    have hz := ht (xor c aL)
      ((mem_eightCandidates_iff aL c).mp hpair.1)
      (by simpa only [xor_xor_cancel] using hneq)
    have hcol := hz
    rw [xor_xor_cancel] at hcol
    omega

/-- Exact DDT entry: one of the eight offsets contributes a fixed 2^29
    factor; all other requested differences give zero. -/
theorem even_zeroLeftDDT_exact
    (k₀ k₁ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) =
      (if xor bR aL ∈ eightOffsets then 2 ^ 29 else 0) *
        xorDDT_g k₁ bR (1#32) := by
  rw [xorDDT_rounds_three_zero_left_factorization,
    even_first_factor k₀ aL bR hk]

/-- Eight tests plus one positive diagonal candidate are equivalent to
    zero defect together with a strictly positive exact DDT coefficient. -/
theorem even_zero_defect_positive_iff_eight_tests
    (k₀ k₁ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    (couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR = 0 ∧
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR)) ↔
      ((xor bR aL ∈ eightOffsets ∧
          0 < xorDDT_g k₁ bR (1#32)) ∧
        ∀ d ∈ eightOffsets, xor d aL ≠ bR →
          xorDDT_g k₁ (xor d aL) (1#32) = 0) := by
  rw [even_defect_zero_iff_eight_tests k₀ k₁ k₂ aL bR hk,
    zeroLeftDDT_pos_iff_mem,
    even_overlap_mem_iff k₀ k₁ aL bR hk,
    mem_eightCandidates_iff]
  exact and_comm

/-- A simple sufficient condition: if all eight candidate column entries
    vanish, there are no compatible zero-left trajectories for any bR. -/
theorem even_all_eight_zero_implies_disjoint
    (k₀ k₁ aL : Word) (hk : k₀.toNat % 2 = 0)
    (hz : ∀ d ∈ eightOffsets,
      xorDDT_g k₁ (xor d aL) (1#32) = 0) :
    supportOverlap k₀ k₁ aL (1#32) = ∅ := by
  apply Set.Subset.antisymm
  · intro c hc
    have hpair := (even_overlap_mem_iff k₀ k₁ aL c hk).mp hc
    have hcol := hz (xor c aL) ((mem_eightCandidates_iff aL c).mp hpair.1)
    rw [xor_xor_cancel] at hcol
    exact ((Nat.ne_of_gt hpair.2) hcol).elim
  · exact Set.empty_subset _

end Magma.DifanEvenUnitOverlapEight
