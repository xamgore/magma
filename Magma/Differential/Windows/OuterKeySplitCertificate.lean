module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.DiagonalMasterCountReduction
import Std.Tactic.BVDecide
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Two-word split of a 256-bit Magma master key

We make the *previously hypothetical* `SplitsOuterKeys` certificate
unconditional. First represent the master as eight 32-bit source words.
Then use `Fin.insertNthEquiv` twice to select the two distinct words used
at the outer positions of a three-round window. The six remaining words
are repacked bijectively into `BitVec 192`.

-/

namespace Magma.DiffanOuterKeySplitCertificate

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanDiagonalSupportScheduledWindows
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanDiagonalMasterKeyClasses
open Magma.OneHotFullKeyClassInvariant
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- Reassemble the eight RFC-order source words (leftmost first). -/
private def assemble8 (f : Fin 8 → Word) : Master :=
  f 0 ++ f 1 ++ f 2 ++ f 3 ++ f 4 ++ f 5 ++ f 6 ++ f 7

/-- The RFC base schedule *is* the eight-word view of the master key. -/
def eightWordsEquiv : Master ≃ (Fin 8 → Word) where
  toFun := fun K i => baseRoundKey K i
  invFun := assemble8
  left_inv := by
    intro K
    change assemble8 (fun i : Fin 8 => baseRoundKey K i) = K
    unfold assemble8 baseRoundKey substring
    bv_decide
  right_inv := by
    intro ws
    funext i
    fin_cases i <;>
      (dsimp [assemble8, baseRoundKey, substring]
       generalize ws 0 = w₀
       generalize ws 1 = w₁
       generalize ws 2 = w₂
       generalize ws 3 = w₃
       generalize ws 4 = w₄
       generalize ws 5 = w₅
       generalize ws 6 = w₆
       generalize ws 7 = w₇
       bv_decide)

/-- Reassemble six words in order, retaining exactly 192 free bits. -/
private def assemble6 (f : Fin 6 → Word) : V 192 :=
  f 0 ++ f 1 ++ f 2 ++ f 3 ++ f 4 ++ f 5

/-- This follows the same high-word-first convention as the RFC. -/
private def split6 (K : V 192) (i : Fin 6) : Word :=
  BitVec.extractLsb' (32 * (5 - i.val)) 32 K

/-- Six independent 32-bit words are exactly 192 independent bits. -/
def sixWordsEquiv : (Fin 6 → Word) ≃ V 192 where
  toFun := assemble6
  invFun := split6
  left_inv := by
    intro ws
    funext i
    fin_cases i <;>
      (dsimp [assemble6, split6]
       generalize ws 0 = w₀
       generalize ws 1 = w₁
       generalize ws 2 = w₂
       generalize ws 3 = w₃
       generalize ws 4 = w₄
       generalize ws 5 = w₅
       bv_decide)
  right_inv := by
    intro K
    unfold assemble6 split6
    bv_decide

/-- The coordinate of `j` after removing the distinct coordinate `i`. -/
private def remainingIndex (i j : Fin 8) (hij : i ≠ j) : Fin 7 :=
  (finSuccAboveEquiv i).symm ⟨j, hij.symm⟩

/-- Remove two *different* indices from an eight-word tuple.
    `Fin.insertNthEquiv` is a genuine equivalence: no information is lost. -/
private def selectTwoWords (i j : Fin 8) (hij : i ≠ j) :
    (Fin 8 → Word) ≃ Word × (Word × (Fin 6 → Word)) :=
  ((Fin.insertNthEquiv (fun _ : Fin 8 => Word) i).symm).trans
    (Equiv.prodCongr (Equiv.refl Word)
      ((Fin.insertNthEquiv (fun _ : Fin 7 => Word) (remainingIndex i j hij)).symm))

/-- Reinserting the removed coordinate recovers the original distinct index. -/
private theorem succAbove_remainingIndex (i j : Fin 8) (hij : i ≠ j) :
    i.succAbove (remainingIndex i j hij) = j := by
  exact congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨j, hij.symm⟩)

private theorem selected_first (i j : Fin 8) (hij : i ≠ j) (f : Fin 8 → Word) :
    (selectTwoWords i j hij f).1 = f i := by rfl

private theorem selected_second (i j : Fin 8) (hij : i ≠ j) (f : Fin 8 → Word) :
    (selectTwoWords i j hij f).2.1 = f j := by
  change f (i.succAbove (remainingIndex i j hij)) = f j
  rw [succAbove_remainingIndex i j hij]

/-- The exact bijection promised by `SplitsOuterKeys`, for every one of
    the thirty ordinary three-round windows. -/
def outerSplit (start : Fin 30) :
    Master ≃ Word × (Word × V 192) :=
  eightWordsEquiv.trans
    ((selectTwoWords
      (sourceSlot ⟨start.val, by omega⟩)
      (sourceSlot ⟨start.val + 2, by omega⟩)
      (outer_source_slots_distinct start)).trans
      (Equiv.prodCongr (Equiv.refl Word)
        (Equiv.prodCongr (Equiv.refl Word) sixWordsEquiv)))

/-- No split hypothesis remains: the two coordinates ARE the scheduled
    outer round keys, not independently invented local parameters. -/
theorem outerSplit_correct (start : Fin 30) :
    SplitsOuterKeys start (outerSplit start) := by
  intro K
  constructor
  · change (selectTwoWords
        (sourceSlot ⟨start.val, by omega⟩)
        (sourceSlot ⟨start.val + 2, by omega⟩)
        (outer_source_slots_distinct start)
        (eightWordsEquiv K)).1 =
      roundKey K ⟨start.val, by omega⟩
    rw [selected_first, roundKey_eq_source]
    rfl
  · change (selectTwoWords
        (sourceSlot ⟨start.val, by omega⟩)
        (sourceSlot ⟨start.val + 2, by omega⟩)
        (outer_source_slots_distinct start)
        (eightWordsEquiv K)).2.1 =
      roundKey K ⟨start.val + 2, by omega⟩
    rw [selected_second, roundKey_eq_source]
    rfl

open scoped Classical in
/-- MAIN UNCONDITIONAL COUNT for all actual Magma master keys. -/
theorem count_two_local_classes
    (start : Fin 30) (P Q : Word → Prop) :
    Fintype.card {K : Master //
      P (roundKey K ⟨start.val, by omega⟩) ∧
      Q (roundKey K ⟨start.val + 2, by omega⟩)} =
      Fintype.card {u : Word // P u} *
      Fintype.card {v : Word // Q v} * 2 ^ 192 := by
  classical
  exact count_two_local_classes_of_split start
    (outerSplit start) (outerSplit_correct start) P Q

open scoped Classical in
/-- The entire unit-diagonal support is counted without an extra
    mathematical hypothesis about the master key. -/
theorem unit_diagonal_master_count
    (start : Fin 30) (aL bR : Word) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
        (aL, 1#32) (1#32, bR)} =
      Fintype.card {u : Word // aL ∈ parityRowSupport u} *
      Fintype.card {v : Word // bR ∈ parityRowSupport v} * 2 ^ 192 := by
  classical
  exact unit_diagonal_master_count_of_split start aL bR
    (outerSplit start) (outerSplit_correct start)

open scoped Classical in
/-- The OneHot master-key count becomes unconditional as well. -/
theorem oneHot_diagonal_master_count
    (start : Fin 30) (j : Fin 32) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32)} =
      Fintype.card {u : Word // oneHotLocalClass u j} *
      Fintype.card {v : Word // oneHotLocalClass v j} * 2 ^ 192 := by
  classical
  exact oneHot_diagonal_master_count_of_split start j
    (outerSplit start) (outerSplit_correct start)

end Magma.DiffanOuterKeySplitCertificate
