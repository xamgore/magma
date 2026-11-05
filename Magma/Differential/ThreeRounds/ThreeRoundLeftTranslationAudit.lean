module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.UnitInputAutomaticSymmetryAudit
public import Magma.Differential.EightRounds.ZeroKeyEightColumnSymmetry
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Left-only and diagonal XOR symmetries of the exact three-round Magma slice

The exact zero-left factorization has two distinct sources of translation
symmetry:

* the input-one row of g[k0], which has shift 0x00006000 iff k0 is even;
* the output-one column of g[0], with diagonal shift 0x00500000.

The row shift preserves the genuine three-round coefficient for arbitrary second
and third round keys.  When the second round key is zero, the diagonal shift
also preserves both the selected coefficient and its off-diagonal coupling
defect.  For even k0 these commuting shifts give four transformations.

Conversely, looking at a single positive column coordinate, but all left
input differences, detects every possible left-only shift.  The complete
family of such shifts is {0, 0x00006000} for even k0 and {0} for odd k0.
-/

namespace Magma.DifanThreeRoundLeftTranslationAudit

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.OddUnitInput77
open Magma.DifanThreeRoundCouplingDefect
open Magma.DifanZeroKeyEightColumn
open Magma.DifanZeroKeyEightColumnSymmetry

private abbrev Word :=
  V 32

/-- The only nontrivial even-row translation. -/
def leftMask : Word := 0x00006000#32

/-- A fixed positive coordinate of the zero-key output-one column. -/
def anchor : Word := 0x00300000#32

/-- The zero-left, input-one slice of the three-round DDT. -/
def selected (k₀ k₁ k₂ aL bR : Word) : Nat :=
  xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
    (aL, 1#32) (0#32, bR)

private theorem xor_left_shift (bR aL : Word) (s : Word) :
    xor bR (aL ^^^ s) = (xor bR aL) ^^^ s := by
  unfold xor
  bv_decide

/-- Exact parity-row weights are invariant under the even-row shift. -/
theorem even_row_shift (k d : Word) (hk : k.toNat % 2 = 0) :
    parityRowCount k (d ^^^ leftMask) = parityRowCount k d := by
  calc
    parityRowCount k (d ^^^ leftMask) =
        xorDDT_g k (1#32) (d ^^^ (0x00006000#32)) := by
          exact (one_round_unit_exact k (d ^^^ leftMask)).symm
    _ = xorDDT_g k (1#32) d :=
      Magma.DifanUnitInputAutomaticSymmetryAudit.even_key_DDT_translation k d hk
    _ = parityRowCount k d := one_round_unit_exact k d

/-- The even first-key translation preserves the coefficient for arbitrary
    second and third round keys. -/
theorem even_selected_left_shift
    (k₀ k₁ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    selected k₀ k₁ k₂ (aL ^^^ leftMask) bR =
      selected k₀ k₁ k₂ aL bR := by
  unfold selected
  rw [every_three_round_entry_exact, every_three_round_entry_exact,
    xor_left_shift]
  rw [even_row_shift k₀ (xor bR aL) hk]

/-- The same left-only shift preserves the exact off-diagonal defect
    in the zero-second-key eight-column slice. -/
theorem even_defect_left_shift
    (k₀ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    couplingDefect k₀ (0#32) k₂ (aL ^^^ leftMask) (1#32)
      (0#32) bR =
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR := by
  rw [couplingDefect_eight_parity k₀ k₂ (aL ^^^ leftMask) bR,
      couplingDefect_eight_parity k₀ k₂ aL bR]
  have hsum :
      (∑ c ∈ zeroColumnSupport.erase bR,
          parityRowCount k₀ (xor c (aL ^^^ leftMask))) =
        ∑ c ∈ zeroColumnSupport.erase bR,
          parityRowCount k₀ (xor c aL) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [xor_left_shift, even_row_shift k₀ (xor c aL) hk]
  calc
    (∑ c ∈ zeroColumnSupport.erase bR,
      2 ^ 29 * parityRowCount k₀ (xor c (aL ^^^ leftMask))) =
        2 ^ 29 * (∑ c ∈ zeroColumnSupport.erase bR,
          parityRowCount k₀ (xor c (aL ^^^ leftMask))) := by
            rw [Finset.mul_sum]
    _ = 2 ^ 29 * (∑ c ∈ zeroColumnSupport.erase bR,
          parityRowCount k₀ (xor c aL)) := by rw [hsum]
    _ = ∑ c ∈ zeroColumnSupport.erase bR,
          2 ^ 29 * parityRowCount k₀ (xor c aL) := by
            rw [Finset.mul_sum]

/-- Two independent, commuting translations yield a four-element
    symmetry family for the actual selected three-round coefficient. -/
theorem even_fourfold_selected
    (k₀ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    (selected k₀ (0#32) k₂ (aL ^^^ leftMask) bR =
       selected k₀ (0#32) k₂ aL bR) ∧
    (selected k₀ (0#32) k₂ (Magma.DifanZeroKeyEightColumnSymmetry.translate aL) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) =
       selected k₀ (0#32) k₂ aL bR) ∧
    (selected k₀ (0#32) k₂ ((Magma.DifanZeroKeyEightColumnSymmetry.translate aL) ^^^ leftMask)
       (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) = selected k₀ (0#32) k₂ aL bR) := by
  refine ⟨even_selected_left_shift k₀ (0#32) k₂ aL bR hk, ?_, ?_⟩
  · exact actual_threeRound_translate k₀ k₂ aL bR
  · calc
      selected k₀ (0#32) k₂ ((Magma.DifanZeroKeyEightColumnSymmetry.translate aL) ^^^ leftMask)
          (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) =
        selected k₀ (0#32) k₂ (Magma.DifanZeroKeyEightColumnSymmetry.translate aL) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) :=
          even_selected_left_shift k₀ (0#32) k₂
            (Magma.DifanZeroKeyEightColumnSymmetry.translate aL) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) hk
      _ = selected k₀ (0#32) k₂ aL bR :=
        actual_threeRound_translate k₀ k₂ aL bR

/-- The same four transformations preserve the genuine coupling defect. -/
theorem even_fourfold_defect
    (k₀ k₂ aL bR : Word) (hk : k₀.toNat % 2 = 0) :
    (couplingDefect k₀ (0#32) k₂ (aL ^^^ leftMask) (1#32)
        (0#32) bR = couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ∧
    (couplingDefect k₀ (0#32) k₂ (Magma.DifanZeroKeyEightColumnSymmetry.translate aL) (1#32)
        (0#32) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) =
      couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) ∧
    (couplingDefect k₀ (0#32) k₂ ((Magma.DifanZeroKeyEightColumnSymmetry.translate aL) ^^^ leftMask)
        (1#32) (0#32) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) =
      couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) := by
  refine ⟨even_defect_left_shift k₀ k₂ aL bR hk, ?_, ?_⟩
  · exact actual_couplingDefect_translate k₀ k₂ aL bR
  · calc
      couplingDefect k₀ (0#32) k₂ ((Magma.DifanZeroKeyEightColumnSymmetry.translate aL) ^^^ leftMask)
          (1#32) (0#32) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) =
        couplingDefect k₀ (0#32) k₂ (Magma.DifanZeroKeyEightColumnSymmetry.translate aL)
          (1#32) (0#32) (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) :=
            even_defect_left_shift k₀ k₂ (Magma.DifanZeroKeyEightColumnSymmetry.translate aL)
              (Magma.DifanZeroKeyEightColumnSymmetry.translate bR) hk
      _ = couplingDefect k₀ (0#32) k₂ aL (1#32)
            (0#32) bR :=
        actual_couplingDefect_translate k₀ k₂ aL bR

/-- The four transformations in the even case have four different
    translation masks on the pair (aL,bR). -/
def evenPairShiftMasks : Finset (Word × Word) :=
  {(0#32, 0#32), (leftMask, 0#32),
   (0x00500000#32, 0x00500000#32),
   (leftMask ^^^ (0x00500000#32), 0x00500000#32)}

theorem evenPairShiftMasks_card : evenPairShiftMasks.card = 4 := by decide +kernel

/-! ## Rigidity: a single nonzero second-factor anchor detects ALL rows -/

private theorem anchor_mem_column : anchor ∈ zeroColumnSupport := by decide +kernel

private theorem anchor_factor_pos : 0 < xorDDT_g (0#32) anchor (1#32) := by
  rw [zeroKey_outputOne_exact, ite_eq_left anchor_mem_column]
  norm_num

/-- If EVERY left input has the same coefficient after a left-only
    translation, then the entire first-round row has that symmetry.
    We need only one positive bR anchor to recover all 32-bit row entries. -/
theorem universal_left_implies_row_support
    (k s : Word)
    (hsym : ∀ aL : Word,
      selected k (0#32) (0#32) (aL ^^^ s) anchor =
        selected k (0#32) (0#32) aL anchor)
    (d : Word) :
    (0 < xorDDT_g k (1#32) (d ^^^ s)) ↔
      (0 < xorDDT_g k (1#32) d) := by
  let aL : Word := xor anchor d
  have harg : xor anchor aL = d := by
    dsimp [aL]
    unfold xor
    bv_decide
  have hargShift : xor anchor (aL ^^^ s) = d ^^^ s := by
    dsimp [aL]
    unfold xor
    bv_decide
  have hcoeff := hsym aL
  unfold selected at hcoeff
  rw [every_three_round_entry_exact,
      every_three_round_entry_exact, hargShift, harg] at hcoeff
  calc
    (0 < xorDDT_g k (1#32) (d ^^^ s)) ↔
        (0 < parityRowCount k (d ^^^ s)) := by
          rw [one_round_unit_exact]
    _ ↔ (0 < parityRowCount k (d ^^^ s) *
        xorDDT_g (0#32) anchor (1#32)) :=
          (Nat.mul_pos_iff_of_pos_right anchor_factor_pos).symm
    _ ↔ (0 < parityRowCount k d *
        xorDDT_g (0#32) anchor (1#32)) := by
          rw [hcoeff]
    _ ↔ (0 < parityRowCount k d) :=
          Nat.mul_pos_iff_of_pos_right anchor_factor_pos
    _ ↔ (0 < xorDDT_g k (1#32) d) := by
          rw [one_round_unit_exact]

private theorem xor_support_image (C : Finset Word) (s : Word) (h : ∀ d, (d ^^^ s ∈ C ↔ d ∈ C)) :
    C.image (fun d => d ^^^ s) = C := by
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    rw [← hxd]
    exact (h x).mpr hx
  · intro hd
    refine Finset.mem_image.mpr ⟨d ^^^ s, (h d).mpr hd, ?_⟩
    bv_decide

/-- The parity-specific exact positive support of the certified row. -/
private theorem row_support_iff (k d : Word) :
    d ∈ parityRowSupport k ↔ 0 < xorDDT_g k (1#32) d := by
  by_cases hk : k.toNat % 2 = 0
  · simp only [parityRowSupport, hk, ite_true]
    rw [one_round_unit_exact]
    simp only [parityRowCount, hk, ite_true]
    by_cases hd : d ∈ eightOffsets <;> simp [hd]
  · have hodd : k.toNat % 2 = 1 := by omega
    simp only [parityRowSupport, hk, ite_false]
    exact (odd_key_positive_iff_support k d hodd).symm

attribute [local irreducible] Difan.AutomaticXorOrbits.shifts

/-- Necessary condition: the only left-only shifts visible in the
    complete zero-second-key slice depend on the first key's parity. -/
theorem left_shift_necessary (k s : Word)
    (hsym : ∀ aL : Word,
      selected k (0#32) (0#32) (aL ^^^ s) anchor =
        selected k (0#32) (0#32) aL anchor) :
    if k.toNat % 2 = 0 then
      s = (0#32) ∨ s = leftMask
    else s = (0#32) := by
  have hsupport (d : Word) :
      (d ^^^ s ∈ parityRowSupport k ↔ d ∈ parityRowSupport k) := by
    simp only [row_support_iff]
    exact universal_left_implies_row_support k s hsym d
  have hstable :
      (parityRowSupport k).image (fun d => d ^^^ s) =
        parityRowSupport k := xor_support_image (parityRowSupport k) s hsupport
  by_cases hk : k.toNat % 2 = 0
  · simp only [hk, ite_true]
    simp only [parityRowSupport, hk, ite_true] at hstable
    have hne : eightOffsets.Nonempty :=
      ⟨0x00001000#32, by decide⟩
    have ht : s ∈ Difan.AutomaticXorOrbits.shifts eightOffsets :=
      (Difan.AutomaticXorOrbits.mem_shifts_iff
        eightOffsets hne s).mpr hstable
    rw [Magma.DifanUnitInputAutomaticSymmetryAudit.even_shifts_exact] at ht
    simpa only [Finset.mem_insert, Finset.mem_singleton,
      leftMask] using ht
  · simp only [hk, ite_false]
    simp only [parityRowSupport, hk, ite_false] at hstable
    have hne : oddOutputSupport.Nonempty :=
      ⟨0x00001000#32, by decide +kernel⟩
    have ht : s ∈ Difan.AutomaticXorOrbits.shifts oddOutputSupport :=
      (Difan.AutomaticXorOrbits.mem_shifts_iff
        oddOutputSupport hne s).mpr hstable
    rw [Magma.DifanUnitInputAutomaticSymmetryAudit.odd_shifts_exact] at ht
    exact Finset.mem_singleton.mp ht

/-- Complete classification of translations of ONLY aL that preserve
    EVERY selected 3-round coefficient, for ALL remaining round keys.
    Even k0: {0, 0x6000}. Odd k0: {0}. -/
theorem uniform_left_shift_iff (k s : Word) :
    (∀ k₁ k₂ aL bR : Word,
      selected k k₁ k₂ (aL ^^^ s) bR = selected k k₁ k₂ aL bR) ↔
      (if k.toNat % 2 = 0 then
        s = (0#32) ∨ s = leftMask
       else s = (0#32)) := by
  constructor
  · intro h
    exact left_shift_necessary k s (fun aL => h (0#32) (0#32) aL anchor)
  · intro h
    by_cases hk : k.toNat % 2 = 0
    · simp only [hk, ite_true] at h
      rcases h with hzero | hmask
      · subst s
        intro k₁ k₂ aL bR
        simp only [BitVec.xor_zero]
      · subst s
        intro k₁ k₂ aL bR
        exact even_selected_left_shift k k₁ k₂ aL bR hk
    · simp only [hk, ite_false] at h
      subst s
      intro k₁ k₂ aL bR
      simp only [BitVec.xor_zero]

end Magma.DifanThreeRoundLeftTranslationAudit
