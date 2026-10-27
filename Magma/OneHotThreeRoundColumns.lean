module

public import Magma.OneHotFullKeyClassInvariant
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Universal one-bit support of zero-left three-round columns

The zero-left three-round DDT factors through the second-round DDT.
An entire one-bit right-output column vanishes precisely when its bit is
excluded by the local class of the second key, independently of the first
and third keys. Every allowed column contains a positive coefficient.

All 32 one-bit columns vanish exactly when key nibble five equals eight
and carry one is unattainable from the low twenty key bits. With the same
nibble and carry one attainable, exactly columns 20 and 22 contain positive
entries.
These results use the unconditional full-word classification and require
no Boolean certificate hypotheses.
-/

namespace Magma.OneHotThreeRoundColumns

open Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotKeyClasses
open Magma.OneHotFullKeyClassInvariant

/-- The one-hot right output difference of a three-round Feistel transition. -/
def bitOutput (j : Fin 32) : V 32 :=
  BitVec.ofNat 32 (2 ^ j.val)

/-- The *local* key-class criterion, using only four candidate bits
    and the nibble/carry invariants of the SECOND round key. -/
def classAllowsBit (k : V 32) (j : Fin 32) : Prop :=
  ∃ r : Fin 4,
    j.val = 20 + r.val ∧
      r ∈ localOneHotSupportedBits
        (keyNibble5 k) (canCarryIntoNibble5 k)

/-- Exact one-hot support of a single Magma round for EVERY key.
    This result has NO Boolean-certificate hypothesis. -/
theorem g_oneHot_positive_iff_class (k : V 32) (j : Fin 32) :
    0 < xorDDT_g k (bitOutput j) (1#32) ↔ classAllowsBit k j := by
  exact oneHot_all_pos_iff_localTable k j

/-- Complete classification of zero-left one-hot three-round columns.
    Both outer round keys are arbitrary; only the SECOND key enters
    the test.  The quantifier over 2^32 possible aL is symbolic. -/
theorem column_all_zero_iff_not_class
    (k₀ k₁ k₂ : V 32) (j : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) = 0) ↔
      ¬ classAllowsBit k₁ j := by
  constructor
  · intro hzero hclass
    have hgzero : xorDDT_g k₁ (bitOutput j) (1#32) = 0 :=
      (zeroLeft_column_empty_iff k₀ k₁ k₂ (1#32) (bitOutput j)).mp hzero
    have hgpos : 0 < xorDDT_g k₁ (bitOutput j) (1#32) :=
      (g_oneHot_positive_iff_class k₁ j).mpr hclass
    omega
  · intro hnot
    apply (zeroLeft_column_empty_iff k₀ k₁ k₂ (1#32) (bitOutput j)).mpr
    apply Nat.eq_zero_of_not_pos
    intro hgpos
    exact hnot ((g_oneHot_positive_iff_class k₁ j).mp hgpos)

/-- A class-allowed column contains an actual positive DDT coefficient,
    for every choice of the first and third round keys.

    This is an existential theorem about aL, not a computational witness
    extractor. It follows from the exact row/column impossibility theorem. -/
theorem column_has_positive_entry_iff_class
    (k₀ k₁ k₂ : V 32) (j : Fin 32) :
    (∃ aL : V 32,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j)) ↔
      classAllowsBit k₁ j := by
  classical
  constructor
  · rintro ⟨aL, hp⟩
    by_contra hnot
    have hall :=
      (column_all_zero_iff_not_class k₀ k₁ k₂ j).mpr hnot
    have hzero := hall aL
    omega
  · intro hclass
    by_contra hnone
    have hall : ∀ aL : V 32,
        xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
          (aL, 1#32) (0#32, bitOutput j) = 0 := by
      intro aL
      apply Nat.eq_zero_of_not_pos
      intro hp
      exact hnone ⟨aL, hp⟩
    exact ((column_all_zero_iff_not_class k₀ k₁ k₂ j).mp hall) hclass

/-- The full support of one-hot three-round columns depends on
    the second-round key only through its sixth nibble and the
    reachability of a carry from its lower 20 bits. -/
theorem columns_same_class
    (k₀ k₁ k₂ k₀' k₁' k₂' : V 32)
    (hq : keyNibble5 k₁ = keyNibble5 k₁')
    (hc : canCarryIntoNibble5 k₁ = canCarryIntoNibble5 k₁')
    (j : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) = 0) ↔
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀' k₁' k₂')
        (aL, 1#32) (0#32, bitOutput j) = 0) := by
  rw [column_all_zero_iff_not_class, column_all_zero_iff_not_class]
  simp only [classAllowsBit, hq, hc]

/-- A finite 4-bit arithmetic fact: among all 32 local key classes,
    precisely (q=8, carry-regime=false) has EMPTY support. -/
theorem local_support_empty_iff
    (q : Fin 16) (c : Bool) :
    localOneHotSupportedBits q c = [] ↔
      q = 8 ∧ c = false := by
  fin_cases q <;> cases c <;> decide

/-- ALL 32 one-hot output columns are zero precisely when the four-bit
    local support list is empty. The quantifier over aL is NOT evaluated. -/
theorem all_columns_zero_iff_local_empty
    (k₀ k₁ k₂ : V 32) :
    (∀ j : Fin 32, ∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) = 0) ↔
      localOneHotSupportedBits
        (keyNibble5 k₁) (canCarryIntoNibble5 k₁) = [] := by
  constructor
  · intro hall
    cases hlist : localOneHotSupportedBits
        (keyNibble5 k₁) (canCarryIntoNibble5 k₁) with
    | nil => rfl
    | cons r rs =>
        let j : Fin 32 := ⟨20 + r.val, by omega⟩
        have hj : classAllowsBit k₁ j := by
          refine ⟨r, rfl, ?_⟩
          rw [hlist]
          simp
        have hnot := (column_all_zero_iff_not_class k₀ k₁ k₂ j).mp (hall j)
        exact False.elim (hnot hj)
  · intro hempty j
    apply (column_all_zero_iff_not_class k₀ k₁ k₂ j).mpr
    rintro ⟨r, _, hr⟩
    rw [hempty] at hr
    exact List.not_mem_nil hr

/-- UNIVERSAL key-class characterization: every one-hot zero-left
    three-round column is impossible iff nibble 5 of the second key
    equals 8 and the lowest 20 key bits are all zero.

    No assumption on k0/k2 and no experiment/certificate premise. -/
theorem all_columns_zero_iff_key_class
    (k₀ k₁ k₂ : V 32) :
    (∀ j : Fin 32, ∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) = 0) ↔
      keyNibble5 k₁ = 8 ∧ canCarryIntoNibble5 k₁ = false := by
  rw [all_columns_zero_iff_local_empty]
  exact local_support_empty_iff
    (keyNibble5 k₁) (canCarryIntoNibble5 k₁)

/-- In the complementary carry regime of nibble-8, exactly output
    positions 20 and 22 have a nonzero three-round column. -/
theorem nibble8_with_carry_column_positive_iff
    (k₀ k₁ k₂ : V 32)
    (hq : keyNibble5 k₁ = 8)
    (hc : canCarryIntoNibble5 k₁ = true)
    (j : Fin 32) :
    (∃ aL : V 32,
      0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j)) ↔
      j.val = 20 ∨ j.val = 22 := by
  rw [column_has_positive_entry_iff_class]
  unfold classAllowsBit
  rw [hq, hc]
  have ht : localOneHotSupportedBits (8 : Fin 16) true = [0, 2] := by
    decide
  rw [ht]
  constructor
  · rintro ⟨r, hj, hr⟩
    have hr' : r = 0 ∨ r = 2 := by simpa using hr
    rcases hr' with hr' | hr'
    · left
      simpa [hr'] using hj
    · right
      simpa [hr'] using hj
  · rintro (hj | hj)
    · refine ⟨0, ?_, by simp⟩
      simp [hj]
    · refine ⟨2, ?_, by simp⟩
      simp [hj]

/-- A concrete member of the exceptional class: key 0x00800000
    rules out all one-hot zero-left columns, with arbitrary outer keys. -/
theorem key_00800000_all_columns_zero
    (k₀ k₂ : V 32) (j : Fin 32) (aL : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0x00800000#32) k₂)
      (aL, 1#32) (0#32, bitOutput j) = 0 := by
  have hc : keyNibble5 (0x00800000#32) = (8 : Fin 16) ∧
      canCarryIntoNibble5 (0x00800000#32) = false := by
    decide
  exact (all_columns_zero_iff_key_class
    k₀ (0x00800000#32) k₂).mpr hc j aL

end Magma.OneHotThreeRoundColumns
