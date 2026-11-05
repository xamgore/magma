module

import all Init.Data.Range.Basic
public import Magma.Differential.EightRounds.ZeroKeyEightSharpBound
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Multiplicity of the zero-second-key eight-column overlap

The only possible nonempty left differences are XORs
of an element in the certified 77-entry odd unit row and an element in
the certified eight-entry zero-key column (at most 77 * 8 pairs).

For every odd first-round key the multiplicity distribution is:

  cardinality 1 : 540 left input differences
  cardinality 2 :   6
  cardinality 3 :  12
  cardinality 4 :   4
  cardinality 5 :   0
  cardinality 6 :   2

The 24 differences of multiplicity at least two are tabulated explicitly.
They occupy only two 28-bit projection classes. The remaining 2^32 - 564
left differences have empty intersection.
-/

namespace Magma.DifanZeroKeyEightMultiplicity

open Magma
open Magma.OddUnitInput77
open Magma.DifanZeroKeyEightColumn
open Magma.DifanZeroKeyEightSharpBound
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

/-- Reuse only the positive support of the 77-entry odd row. -/
def oddSurvivors (aL : Word) : Finset Word :=
  zeroColumnSupport.filter (fun c => xor c aL ∈ oddOutputSupport)

/-- For arbitrary ODD k0, the exact survivors depend only on aL. -/
theorem odd_survivors_eq (k₀ aL : Word) (hk : k₀.toNat % 2 = 1) :
    survivingCandidates k₀ aL = oddSurvivors aL := by
  ext c
  rw [odd_surviving_iff k₀ aL c hk]
  simp only [oddSurvivors, Finset.mem_filter]

/-- The *finite* candidate domain, generated from 77 * 8 pairs.
    Duplicates are automatically removed by `Finset.image`. -/
def oddCandidateInputs : Finset Word :=
  (oddOutputSupport.product zeroColumnSupport).image
    (fun dc : Word × Word => xor dc.1 dc.2)

section

attribute [local irreducible] oddOutputSupport zeroColumnSupport

/-- A left difference has any survivors iff it belongs to the finite
    domain of XOR pairs. The proof is symbolic in aL, not a full-word scan. -/
theorem candidate_iff_nonempty (aL : Word) :
    aL ∈ oddCandidateInputs ↔ (oddSurvivors aL).Nonempty := by
  constructor
  · intro ha
    obtain ⟨⟨d, c⟩, hdc, heq⟩ := Finset.mem_image.mp ha
    obtain ⟨hd, hc⟩ := Finset.mem_product.mp hdc
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩⟩
    have h : xor c aL = d := by
      change xor d c = aL at heq
      rw [← heq]
      unfold xor
      bv_decide
    rw [h]
    exact hd
  · rintro ⟨c, hc⟩
    obtain ⟨hcol, hrow⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_image.mpr
    refine ⟨(xor c aL, c), Finset.mem_product.mpr ⟨hrow, hcol⟩, ?_⟩
    change xor (xor c aL) c = aL
    unfold xor
    bv_decide

/-- Exactly 564 values of aL have any overlap at an odd first key. -/
theorem oddCandidateInputs_card : oddCandidateInputs.card = 564 := by
  decide +kernel

attribute [local irreducible] oddCandidateInputs

/-- The complete 24-element table for multiplicity at least two. -/
def multipleInputTable : Finset Word :=
  {0x000CE800#32, 0x001CE800#32, 0x002CE800#32,
   0x0034E800#32, 0x004CE800#32, 0x005CE800#32,
   0x0064E800#32, 0x007CE800#32, 0x0084E800#32,
   0x008CE800#32, 0x0094E800#32, 0x009CE800#32,
   0x00A4E800#32, 0x00ACE800#32, 0x00B4E800#32,
   0x00BCE800#32, 0x00C4E800#32, 0x00CCE800#32,
   0x00D4E800#32, 0x00DCE800#32, 0x00E4E800#32,
   0x00ECE800#32, 0x00F4E800#32, 0x00FCE800#32}

/-- The explicit table consists exactly of candidate left differences
    admitting at least two surviving intermediate differences. -/
theorem multipleInputTable_exact :
    oddCandidateInputs.filter
        (fun aL => 2 ≤ (oddSurvivors aL).card) = multipleInputTable := by
  decide +kernel

/-- Consequently the two-or-more class has exactly 24 elements. -/
theorem multipleInputTable_card : multipleInputTable.card = 24 := by
  decide +kernel

/-- A table of the ONLY two 28-bit masks permitting multiplicity >= 2. -/
def collisionMasks : Finset Word :=
  {0x0004E800#32, 0x000CE800#32}

attribute [local irreducible] multipleInputTable collisionMasks

private theorem multipleInputTable_mask :
    ∀ aL ∈ multipleInputTable, clearNibble5 aL ∈ collisionMasks := by
  have hempty : (multipleInputTable.filter (fun aL => clearNibble5 aL ∉ collisionMasks)) = ∅ := by
    decide +kernel
  intro aL ha
  by_contra hn
  have hmem : aL ∈ multipleInputTable.filter (fun aL => clearNibble5 aL ∉ collisionMasks) :=
    Finset.mem_filter.mpr ⟨ha, hn⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty aL hmem

/-- The table classifies multiplicity at least two for every odd first key. -/
theorem odd_multiple_iff (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    2 ≤ (survivingCandidates k₀ aL).card ↔
      aL ∈ multipleInputTable := by
  rw [odd_survivors_eq k₀ aL hk]
  constructor
  · intro hm
    have hn : (oddSurvivors aL).Nonempty :=
      Finset.card_pos.mp (by omega : 0 < (oddSurvivors aL).card)
    have hc : aL ∈ oddCandidateInputs :=
      (candidate_iff_nonempty aL).mpr hn
    rw [← multipleInputTable_exact]
    exact Finset.mem_filter.mpr ⟨hc, hm⟩
  · intro ht
    have hm : aL ∈ oddCandidateInputs.filter
        (fun x => 2 ≤ (oddSurvivors x).card) := by
      rw [multipleInputTable_exact]
      exact ht
    exact (Finset.mem_filter.mp hm).2

/-- An immediate strengthening of the earlier six-mask necessary
    condition: only TWO masks can cause a genuine collision. -/
theorem odd_multiple_forces_two_masks (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1)
    (hm : 2 ≤ (survivingCandidates k₀ aL).card) :
    clearNibble5 aL ∈ collisionMasks :=
  multipleInputTable_mask aL ((odd_multiple_iff k₀ aL hk).mp hm)

/-- For any odd first key, exactly the 564 finite candidate inputs
    have at least one surviving intermediate difference. -/
theorem odd_nonempty_iff (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    (survivingCandidates k₀ aL).Nonempty ↔
      aL ∈ oddCandidateInputs := by
  rw [odd_survivors_eq k₀ aL hk]
  exact (candidate_iff_nonempty aL).symm

/-- One class consists of 10 multiple-survivor words, the other of 14. -/
theorem two_mask_counts :
    (multipleInputTable.filter
        (fun aL => clearNibble5 aL = (0x0004E800#32))).card = 10 ∧
    (multipleInputTable.filter
        (fun aL => clearNibble5 aL = (0x000CE800#32))).card = 14 := by
  constructor <;> decide +kernel

/-- Levels >= 2 need only scan the explicit 24-element table. -/
def multipleLevel (n : Nat) : Finset Word :=
  multipleInputTable.filter (fun aL => (oddSurvivors aL).card = n)

/-- The complete 24-word multiplicity distribution, including the gap at 5. -/
theorem multipleLevel_counts :
    (multipleLevel 2).card = 6 ∧
    (multipleLevel 3).card = 12 ∧
    (multipleLevel 4).card = 4 ∧
    (multipleLevel 5).card = 0 ∧
    (multipleLevel 6).card = 2 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel

/-- Exact classification of every multiplicity n >= 2, valid
    uniformly for all odd first-round keys. -/
theorem odd_multipleLevel_iff (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) (n : Nat) (hn : 2 ≤ n) :
    (survivingCandidates k₀ aL).card = n ↔
      aL ∈ multipleLevel n := by
  constructor
  · intro h
    have hm : 2 ≤ (survivingCandidates k₀ aL).card := by omega
    have ht : aL ∈ multipleInputTable :=
      (odd_multiple_iff k₀ aL hk).mp hm
    exact Finset.mem_filter.mpr ⟨ht, by
      simpa only [odd_survivors_eq k₀ aL hk] using h⟩
  · intro h
    have hn' := (Finset.mem_filter.mp h).2
    rw [odd_survivors_eq k₀ aL hk]
    exact hn'

/-- The 540 singleton values are precisely the nonempty inputs outside
    the two-or-more table. -/
def singletonInputs : Finset Word :=
  oddCandidateInputs \ multipleInputTable

theorem multipleInputTable_subset : multipleInputTable ⊆ oddCandidateInputs := by
  rw [← multipleInputTable_exact]
  exact Finset.filter_subset _ _

/-- A left input has exactly one compatible middle difference iff
    it belongs to the singleton table. -/
theorem odd_singleton_iff (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    (survivingCandidates k₀ aL).card = 1 ↔
      aL ∈ singletonInputs := by
  rw [odd_survivors_eq k₀ aL hk]
  simp only [singletonInputs, Finset.mem_sdiff]
  constructor
  · intro h1
    have hc : aL ∈ oddCandidateInputs :=
      (candidate_iff_nonempty aL).mpr
        (Finset.card_pos.mp (by omega : 0 < (oddSurvivors aL).card))
    refine ⟨hc, ?_⟩
    intro hm
    have hh : aL ∈ oddCandidateInputs.filter
        (fun x => 2 ≤ (oddSurvivors x).card) := by
      rw [multipleInputTable_exact]
      exact hm
    have h2 : 2 ≤ (oddSurvivors aL).card :=
      (Finset.mem_filter.mp hh).2
    omega
  · rintro ⟨hc, hnot⟩
    have hp : 0 < (oddSurvivors aL).card :=
      Finset.card_pos.mpr ((candidate_iff_nonempty aL).mp hc)
    have hn : ¬ (2 ≤ (oddSurvivors aL).card) := by
      intro h2
      apply hnot
      have hh : aL ∈ oddCandidateInputs.filter
          (fun x => 2 ≤ (oddSurvivors x).card) :=
        Finset.mem_filter.mpr ⟨hc, h2⟩
      rw [multipleInputTable_exact] at hh
      exact hh
    omega

/-- Proof by subtraction, not another 564-by-8 scan. -/
theorem singletonInputs_card : singletonInputs.card = 540 := by
  rw [singletonInputs, Finset.card_sdiff_of_subset multipleInputTable_subset,
    oddCandidateInputs_card, multipleInputTable_card]

end

end Magma.DifanZeroKeyEightMultiplicity
