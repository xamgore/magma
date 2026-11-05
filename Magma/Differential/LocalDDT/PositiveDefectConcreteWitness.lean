module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.OddUnitLow20CollisionClasses

@[expose] public section

/-!
# A positive DDT entry with strictly positive coupling defect

The six exceptional low-20 prefixes of OddUnitLow20CollisionClasses were
necessary candidates for genuine coupling. Here we show that coupling really
occurs: at prefix `0xCE800`, first key 1 and second key 0, the shifted
77-element row and the second-key output-one column intersect at three
explicit intermediate differences.

Each second-column witness supplies a concrete base word realizing the
transition. First-row positivity follows from membership in the certified
77-entry support table.
-/

namespace Magma.DifanPositiveDefectConcreteWitness

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanUnitColumnLow20AndUniqueEven
open Magma.OddUnitInput77
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanOddUnitLow20CollisionClasses
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- The shared left input difference and three distinct intermediate words. -/
def witnessAL : Word := 0x000CE800#32

def candidate0 : Word :=
  0x00300000#32

def candidate1 : Word :=
  0x00600000#32

def candidate2 : Word :=
  0x00D00000#32

/-- A concrete input realizing the transition witnesses positivity
    of the corresponding DDT coefficient. -/
private theorem zeroKey_column_pos_of_point
    (d x : Word)
    (hx : xor (g (0#32) (xor x d)) (g (0#32) x) = (1#32)) :
    0 < xorDDT_g (0#32) d (1#32) := by
  unfold xorDDT_g
  apply Finset.card_pos.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- A concrete base input realizes the first candidate transition. -/
theorem column_pos_0 :
    0 < xorDDT_g (0#32) candidate0 (1#32) := by
  apply zeroKey_column_pos_of_point candidate0 (0x00100000#32)
  decide

theorem column_pos_1 : 0 < xorDDT_g (0#32) candidate1 (1#32) := by
  apply zeroKey_column_pos_of_point candidate1 (0x00B00000#32)
  decide

theorem column_pos_2 : 0 < xorDDT_g (0#32) candidate2 (1#32) := by
  apply zeroKey_column_pos_of_point candidate2 (0x00700000#32)
  decide

/-- Membership in the complete odd-key row support implies positivity. -/
private theorem odd_row_pos (c : Word)
    (hc : xor c witnessAL ∈ oddOutputSupport) :
    0 < xorDDT_g (1#32) (1#32) (xor c witnessAL) := by
  apply (odd_key_positive_iff_support (1#32) _ (by decide)).mpr
  exact hc

theorem row_pos_0 : 0 < xorDDT_g (1#32) (1#32) (xor candidate0 witnessAL) := by
  apply odd_row_pos
  decide +kernel

theorem row_pos_1 : 0 < xorDDT_g (1#32) (1#32) (xor candidate1 witnessAL) := by
  apply odd_row_pos
  decide +kernel

theorem row_pos_2 : 0 < xorDDT_g (1#32) (1#32) (xor candidate2 witnessAL) := by
  apply odd_row_pos
  decide +kernel

/-- The actual shifted row/column overlap includes three distinct words. -/
theorem overlap_contains_three :
    candidate0 ∈ supportOverlap (1#32) (0#32) witnessAL (1#32) ∧
    candidate1 ∈ supportOverlap (1#32) (0#32) witnessAL (1#32) ∧
    candidate2 ∈ supportOverlap (1#32) (0#32) witnessAL (1#32) := by
  exact ⟨⟨row_pos_0, column_pos_0⟩,
    ⟨row_pos_1, column_pos_1⟩,
    ⟨row_pos_2, column_pos_2⟩⟩

/-- The same three positive candidates exist for EVERY odd first key,
    because the entire unit-input row depends only on key parity. -/
theorem odd_first_overlap_contains_three (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    candidate0 ∈ supportOverlap k₀ (0#32) witnessAL (1#32) ∧
    candidate1 ∈ supportOverlap k₀ (0#32) witnessAL (1#32) ∧
    candidate2 ∈ supportOverlap k₀ (0#32) witnessAL (1#32) := by
  have hrow0 :
      0 < xorDDT_g k₀ (1#32) (xor candidate0 witnessAL) :=
    (odd_key_positive_iff_support k₀ _ hk).mpr (by decide +kernel)
  have hrow1 :
      0 < xorDDT_g k₀ (1#32) (xor candidate1 witnessAL) :=
    (odd_key_positive_iff_support k₀ _ hk).mpr (by decide +kernel)
  have hrow2 :
      0 < xorDDT_g k₀ (1#32) (xor candidate2 witnessAL) :=
    (odd_key_positive_iff_support k₀ _ hk).mpr (by decide +kernel)
  exact ⟨⟨hrow0, column_pos_0⟩,
    ⟨hrow1, column_pos_1⟩,
    ⟨hrow2, column_pos_2⟩⟩

/-- For every odd k₀, k₁=0 and arbitrary k₂, the selected
    three-round DDT entry is positive and has a
    strictly positive off-diagonal coupling defect on this slice. -/
theorem all_odd_first_positive_ddt_and_defect
    (k₀ k₂ : Word) (hk : k₀.toNat % 2 = 1) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (witnessAL, 1#32) (0#32, candidate0) ∧
    0 < couplingDefect k₀ (0#32) k₂
      witnessAL (1#32) (0#32) candidate0 := by
  obtain ⟨h0, h1, _⟩ := odd_first_overlap_contains_three k₀ hk
  constructor
  · exact (zeroLeftDDT_pos_iff_mem
      k₀ (0#32) k₂ witnessAL (1#32) candidate0).mpr h0
  · apply (couplingDefect_pos_iff_exists_offDiagonal
      k₀ (0#32) k₂ witnessAL (1#32) candidate0).mpr
    refine ⟨candidate1, ?_, h1⟩
    decide

/-- A nonzero real three-round DDT coefficient, for every last key. -/
theorem concrete_threeRound_positive (k₂ : Word) :
    0 < xorDDT_rounds 3 (threeRoundKeys (1#32) (0#32) k₂)
      (witnessAL, 1#32) (0#32, candidate0) := by
  exact (zeroLeftDDT_pos_iff_mem
    (1#32) (0#32) k₂ witnessAL (1#32) candidate0).mpr
    overlap_contains_three.1

/-- The simultaneously positive coefficient and strictly positive defect
    show that the six exceptional prefixes are not just an artefact of
    the necessary-condition proof. -/
theorem concrete_positive_defect (k₂ : Word) :
    0 < couplingDefect (1#32) (0#32) k₂
      witnessAL (1#32) (0#32) candidate0 := by
  apply (couplingDefect_pos_iff_exists_offDiagonal
    (1#32) (0#32) k₂ witnessAL (1#32) candidate0).mpr
  refine ⟨candidate1, ?_, overlap_contains_three.2.1⟩
  decide

/-- Both phenomena occur together, not for different outputs or keys. -/
theorem concrete_positive_coefficient_and_defect (k₂ : Word) :
    0 < xorDDT_rounds 3 (threeRoundKeys (1#32) (0#32) k₂)
      (witnessAL, 1#32) (0#32, candidate0) ∧
    0 < couplingDefect (1#32) (0#32) k₂
      witnessAL (1#32) (0#32) candidate0 := by
  exact ⟨concrete_threeRound_positive k₂, concrete_positive_defect k₂⟩

/-- The witness belongs to the largest of the six collision classes. -/
theorem witness_uses_exceptional_prefix :
    low20 witnessAL = (0xCE800#20) ∧
    low20 witnessAL ∈ oddCollisionPrefixes := by
  constructor <;> decide

end Magma.DifanPositiveDefectConcreteWitness
