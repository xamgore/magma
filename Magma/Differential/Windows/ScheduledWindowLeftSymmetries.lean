module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundLeftTranslationAudit
public import Magma.Differential.Windows.RepeatedWindowIntersections

@[expose] public section

/-!
# Left-translation certificates across the actual Magma key schedule

The previously proved three-round classification is uniform in the second
and third round keys.  Here its first key is selected from one 256-bit
master key by the genuine RFC 8891 schedule.

The uniform certificate for the nonzero translation 0x00006000 is equivalent
to even parity of the corresponding master-key word.  Reusing a scheduled
round key does not create a new independent parity condition.

A theorem about all 30 ordinary three-round windows is proved by reducing
them to the eight original source words, including the reversed final
schedule segment. The conclusions concern the DDTs of these individual
three-round windows.
-/

namespace Magma.DifanScheduledWindowLeftSymmetries

open Magma
open Magma.MultiRoundDDT
open Magma.DifanThreeRoundLeftTranslationAudit
open Magma.DifanDiagonalSupportScheduledWindows
open Magma.DifanDiagonalMasterCountReduction
open Magma.DifanRepeatedWindowIntersections

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- The strong symmetry certificate of one selected first-round key:
    the other two round keys, the left input, and the requested right
    output difference are all universally quantified. -/
def universalAt (K : Master) (start : Fin 30) (t : Word) : Prop :=
  ∀ k₁ k₂ aL bR : Word,
    selected (roundKey K ⟨start.val, by omega⟩)
      k₁ k₂ (aL ^^^ t) bR =
    selected (roundKey K ⟨start.val, by omega⟩)
      k₁ k₂ aL bR

/-- The translation class of a scheduled window depends on the parity
    of its first round key. -/
theorem universalAt_iff (K : Master) (start : Fin 30) (t : Word) :
    universalAt K start t ↔
      (if (roundKey K ⟨start.val, by omega⟩).toNat % 2 = 0 then
        t = (0#32) ∨ t = leftMask
       else t = (0#32)) := by
  exact uniform_left_shift_iff (roundKey K ⟨start.val, by omega⟩) t

/-- The nonzero shift is a certificate exactly when this scheduled
    first-round key is even. -/
theorem leftMask_universal_iff_even (K : Master) (start : Fin 30) :
    universalAt K start leftMask ↔
      (roundKey K ⟨start.val, by omega⟩).toNat % 2 = 0 := by
  constructor
  · intro h
    have hh := (universalAt_iff K start leftMask).mp h
    by_contra hodd
    have hz : leftMask = (0#32) := by
      simpa only [ite_eq_right hodd] using hh
    have hne : leftMask ≠ (0#32) := by decide
    exact hne hz
  · intro heven
    apply (universalAt_iff K start leftMask).mpr
    rw [ite_eq_left heven]
    exact Or.inr rfl

/-- A scheduled window consists of three consecutive round keys. -/
private theorem scheduled_keys_eq_three (K : Master) (start : Fin 30) :
    scheduledThreeKeys K start =
      threeRoundKeys
        (roundKey K ⟨start.val, by omega⟩)
        (roundKey K ⟨start.val + 1, by omega⟩)
        (roundKey K ⟨start.val + 2, by omega⟩) := by
  funext i
  fin_cases i <;> rfl

/-- A true three-round coefficient in the scheduled window inherits the
    nonzero left translation whenever its actual first key is even. -/
theorem actual_window_left_shift (K : Master) (start : Fin 30)
    (aL bR : Word)
    (heven : (roundKey K ⟨start.val, by omega⟩).toNat % 2 = 0) :
    xorDDT_rounds 3 (scheduledThreeKeys K start)
      (aL ^^^ leftMask, 1#32) (0#32, bR) =
    xorDDT_rounds 3 (scheduledThreeKeys K start)
      (aL, 1#32) (0#32, bR) := by
  rw [scheduled_keys_eq_three]
  change selected (roundKey K ⟨start.val, by omega⟩)
      (roundKey K ⟨start.val + 1, by omega⟩)
      (roundKey K ⟨start.val + 2, by omega⟩)
      (aL ^^^ leftMask) bR =
    selected (roundKey K ⟨start.val, by omega⟩)
      (roundKey K ⟨start.val + 1, by omega⟩)
      (roundKey K ⟨start.val + 2, by omega⟩)
      aL bR
  exact even_selected_left_shift
    (roundKey K ⟨start.val, by omega⟩)
    (roundKey K ⟨start.val + 1, by omega⟩)
    (roundKey K ⟨start.val + 2, by omega⟩)
    aL bR heven

/-- For two three-round windows eight rounds apart, the uniform
    translation conditions on both windows are one parity restriction
    on the same master-key word. -/
theorem repeated_pair_universal_iff (K : Master) (s : Fin 14) :
    (universalAt K (earlier s) leftMask ∧
      universalAt K (later s) leftMask) ↔
      (roundKey K ⟨(earlier s).val, by omega⟩).toNat % 2 = 0 := by
  constructor
  · intro h
    exact (leftMask_universal_iff_even K (earlier s)).mp h.1
  · intro heven
    constructor
    · exact (leftMask_universal_iff_even K (earlier s)).mpr heven
    · apply (leftMask_universal_iff_even K (later s)).mpr
      rw [repeated_first_key K s]
      exact heven

/-- Repeated first round keys give symmetry in both scheduled windows,
    even when their queried differences differ. -/
theorem repeated_pair_actual_shift (K : Master) (s : Fin 14)
    (aL₀ bR₀ aL₁ bR₁ : Word)
    (heven : (roundKey K ⟨(earlier s).val, by omega⟩).toNat % 2 = 0) :
    (xorDDT_rounds 3 (scheduledThreeKeys K (earlier s))
       (aL₀ ^^^ leftMask, 1#32) (0#32, bR₀) =
     xorDDT_rounds 3 (scheduledThreeKeys K (earlier s))
       (aL₀, 1#32) (0#32, bR₀)) ∧
    (xorDDT_rounds 3 (scheduledThreeKeys K (later s))
       (aL₁ ^^^ leftMask, 1#32) (0#32, bR₁) =
     xorDDT_rounds 3 (scheduledThreeKeys K (later s))
       (aL₁, 1#32) (0#32, bR₁)) := by
  refine ⟨actual_window_left_shift K (earlier s) aL₀ bR₀ heven, ?_⟩
  apply actual_window_left_shift K (later s) aL₁ bR₁
  rw [repeated_first_key K s]
  exact heven

/-- Uniform translation symmetry in every one of the 30 ordinary
    three-round windows is equivalent to even parity of all eight
    source words of the 256-bit master key.  This uses the actual
    reversal in the last eight rounds. -/
theorem all_windows_iff_eight_source_words_even (K : Master) :
    (∀ start : Fin 30, universalAt K start leftMask) ↔
      (∀ i : Fin 8, (baseRoundKey K i).toNat % 2 = 0) := by
  constructor
  · intro h i
    have hi :=
      (leftMask_universal_iff_even K ⟨i.val, by omega⟩).mp
        (h ⟨i.val, by omega⟩)
    simpa only [roundKey_first] using hi
  · intro heven start
    apply (leftMask_universal_iff_even K start).mpr
    rw [roundKey_eq_source]
    exact heven (sourceSlot ⟨start.val, by omega⟩)

/-- The all-eight-word parity condition supplies an actual left-shift
    equality for every scheduled three-round window, with its genuine
    second and third round keys. -/
theorem all_windows_actual_shift (K : Master)
    (heven : ∀ i : Fin 8, (baseRoundKey K i).toNat % 2 = 0)
    (start : Fin 30) (aL bR : Word) :
    xorDDT_rounds 3 (scheduledThreeKeys K start)
      (aL ^^^ leftMask, 1#32) (0#32, bR) =
    xorDDT_rounds 3 (scheduledThreeKeys K start)
      (aL, 1#32) (0#32, bR) := by
  apply actual_window_left_shift K start aL bR
  rw [roundKey_eq_source]
  exact heven (sourceSlot ⟨start.val, by omega⟩)

end Magma.DifanScheduledWindowLeftSymmetries
