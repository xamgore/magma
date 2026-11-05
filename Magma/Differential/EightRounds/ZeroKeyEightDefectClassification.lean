module

import all Init.Data.Range.Basic
public import Magma.Differential.EightRounds.ZeroKeyEightMultiplicity

@[expose] public section

/-!
# Exact positive-defect classification from eight-column multiplicities

For the zero-left three-round slice

  (aR, bL, k1) = (1, 0, 0),

let S(k0,aL) be the certified set `survivingCandidates k0 aL`.
A selected three-round coefficient at bR is positive exactly when bR
belongs to S. Its coupling defect is positive precisely when another
member of S, distinct from bR, is present.

Consequently, *when the selected coefficient is positive*, positive
defect is equivalent to |S| >= 2. The assumption about the selected
coefficient matters: an unselected bR can have positive defect even
when |S| = 1.

The proved 24-word multiplicity table makes the exact classification
uniform in all odd first-round keys and all third-round keys. The
resulting set of (aL,bR) pairs has size 76 = 6*2 + 12*3 + 4*4 + 2*6.
These statements concern exact counts of concrete-state fibers, not
products of independently sampled differential transitions.
-/

namespace Magma.DiffanZeroKeyEightDefectClassification

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanZeroKeyEightColumn
open Magma.DiffanZeroKeyEightSharpBound
open Magma.DiffanZeroKeyEightMultiplicity

private abbrev Word :=
  V 32

/-- The chosen three-round coefficient is positive iff the chosen middle
    difference belongs to the *actual* eight-column overlap. -/
theorem selected_positive_iff (k₀ k₂ aL bR : Word) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ↔
      bR ∈ survivingCandidates k₀ aL := by
  rw [zeroLeftDDT_pos_iff_mem]
  exact (survivingCandidates_iff_overlap k₀ aL bR).symm

/-- Even when the chosen three-round coefficient is zero, the defect
    may be positive: it records the OTHER compatible middle values. -/
theorem defect_positive_iff_other (k₀ k₂ aL bR : Word) :
    0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR ↔
      ∃ c ∈ survivingCandidates k₀ aL, c ≠ bR := by
  rw [couplingDefect_pos_iff_exists_offDiagonal]
  constructor
  · rintro ⟨c, hne, hc⟩
    exact ⟨c, (survivingCandidates_iff_overlap k₀ aL c).mpr hc, hne⟩
  · rintro ⟨c, hc, hne⟩
    exact ⟨c, hne, (survivingCandidates_iff_overlap k₀ aL c).mp hc⟩

/-- An arbitrary selected entry has BOTH a positive exact DDT
    coefficient and a positive defect iff it belongs to a nontrivial
    overlap. No condition on the parity of k0 is used here. -/
theorem selected_positive_and_defect_iff (k₀ k₂ aL bR : Word) :
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ↔
      bR ∈ survivingCandidates k₀ aL ∧
        2 ≤ (survivingCandidates k₀ aL).card := by
  rw [selected_positive_iff, defect_positive_iff_other]
  constructor
  · rintro ⟨hb, ⟨c, hc, hne⟩⟩
    refine ⟨hb, ?_⟩
    have hsub : ({bR, c} : Finset Word) ⊆
        survivingCandidates k₀ aL := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    have hcard : ({bR, c} : Finset Word).card = 2 := by
      have hne' : bR ≠ c := Ne.symm hne
      simp [hne']
    calc
      2 = ({bR, c} : Finset Word).card := hcard.symm
      _ ≤ (survivingCandidates k₀ aL).card := Finset.card_le_card hsub
  · rintro ⟨hb, htwo⟩
    refine ⟨hb, ?_⟩
    by_contra hn
    have hunique : ∀ c ∈ survivingCandidates k₀ aL, c = bR := by
      intro c hc
      by_contra hne
      exact hn ⟨c, hc, hne⟩
    have hle : (survivingCandidates k₀ aL).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb'
      exact (hunique a ha).trans (hunique b hb').symm
    omega

/-- The odd-key slice is now controlled *exactly* by the 24-word table,
    rather than merely by the earlier six exceptional masks. -/
theorem odd_selected_positive_and_defect_iff
    (k₀ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 1) :
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ↔
      bR ∈ oddSurvivors aL ∧ aL ∈ multipleInputTable := by
  rw [selected_positive_and_defect_iff]
  constructor
  · rintro ⟨hb, hm⟩
    exact ⟨by simpa only [odd_survivors_eq k₀ aL hk] using hb,
      (odd_multiple_iff k₀ aL hk).mp hm⟩
  · rintro ⟨hb, ht⟩
    exact ⟨by simpa only [odd_survivors_eq k₀ aL hk] using hb,
      (odd_multiple_iff k₀ aL hk).mpr ht⟩

/-- Pairs of left inputs and selected outputs with both positive
    three-round coefficient and positive coupling defect. -/
def positiveDefectPairs : Finset (Word × Word) :=
  (multipleInputTable.product zeroColumnSupport).filter
    (fun p => p.2 ∈ oddSurvivors p.1)

theorem mem_positiveDefectPairs_iff (aL bR : Word) :
    (aL, bR) ∈ positiveDefectPairs ↔ aL ∈ multipleInputTable ∧ bR ∈ oddSurvivors aL := by
  constructor
  · intro hp
    obtain ⟨hprod, hb⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_product.mp hprod).1, hb⟩
  · rintro ⟨ha, hb⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨ha, (Finset.mem_filter.mp hb).1⟩, hb⟩

/-- At every odd k0 and every k2, the positive-DDT/positive-defect
    pairs coincide with the SAME 76-member finite set. -/
theorem odd_positive_defect_pair_iff (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1) :
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ↔
      (aL, bR) ∈ positiveDefectPairs := by
  rw [odd_selected_positive_and_defect_iff k₀ k₂ aL bR hk,
    mem_positiveDefectPairs_iff]
  exact and_comm

/-- Only 24*8 table entries are inspected. In particular, 76 counts
    PAIRS (aL,bR), whereas 24 counts only different left inputs. -/
theorem positiveDefectPairs_card : positiveDefectPairs.card = 76 := by
  decide +kernel

/-- A left difference admits SOME selected positive coefficient with
    positive defect iff it is one of the 24 certified words. -/
theorem odd_exists_positive_and_defect_iff
    (k₀ k₂ aL : Word) (hk : k₀.toNat % 2 = 1) :
    (∃ bR : Word,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ↔
      aL ∈ multipleInputTable := by
  constructor
  · rintro ⟨bR, h⟩
    exact ((odd_selected_positive_and_defect_iff k₀ k₂ aL bR hk).mp h).2
  · intro ht
    have hm : 2 ≤ (survivingCandidates k₀ aL).card :=
      (odd_multiple_iff k₀ aL hk).mpr ht
    have hpos : 0 < (survivingCandidates k₀ aL).card := by omega
    obtain ⟨bR, hb⟩ := Finset.card_pos.mp hpos
    exact ⟨bR,
      (selected_positive_and_defect_iff k₀ k₂ aL bR).mpr ⟨hb, hm⟩⟩

/-- Independent of parity: positive coefficient and positive defect
    force odd k0, since an even first key has at most one survivor. -/
theorem positive_and_defect_forces_odd_and_table
    (k₀ k₂ aL bR : Word)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, bR))
    (hd : 0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) :
    k₀.toNat % 2 = 1 ∧ aL ∈ multipleInputTable := by
  have hm := ((selected_positive_and_defect_iff k₀ k₂ aL bR).mp ⟨hp, hd⟩).2
  have hk : k₀.toNat % 2 = 1 := by
    by_cases he : k₀.toNat % 2 = 0
    · have hle := even_surviving_card_le_one k₀ aL he
      omega
    · omega
  exact ⟨hk, (odd_multiple_iff k₀ aL hk).mp hm⟩

/-- UNIFORM complete classification across all 32-bit first-round keys.
    The 76 pairs occur exactly for the odd-key class. -/
theorem positive_and_defect_iff_odd_pair (k₀ k₂ aL bR : Word) :
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ↔
      k₀.toNat % 2 = 1 ∧ (aL, bR) ∈ positiveDefectPairs := by
  constructor
  · rintro ⟨hp, hd⟩
    obtain ⟨hk, _⟩ := positive_and_defect_forces_odd_and_table
      k₀ k₂ aL bR hp hd
    exact ⟨hk,
      (odd_positive_defect_pair_iff k₀ k₂ aL bR hk).mp ⟨hp, hd⟩⟩
  · rintro ⟨hk, hp⟩
    exact (odd_positive_defect_pair_iff k₀ k₂ aL bR hk).mpr hp

/-- The six-mask result strengthens to TWO masks for the simultaneous
    positive-coefficient/positive-defect phenomenon. -/
theorem positive_and_defect_forces_two_masks
    (k₀ k₂ aL bR : Word)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, bR))
    (hd : 0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) :
    clearNibble5 aL ∈ collisionMasks := by
  obtain ⟨hk, ht⟩ := positive_and_defect_forces_odd_and_table
    k₀ k₂ aL bR hp hd
  exact odd_multiple_forces_two_masks k₀ aL hk
    ((odd_multiple_iff k₀ aL hk).mpr ht)

end Magma.DiffanZeroKeyEightDefectClassification
