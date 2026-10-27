module

public import Magma.OneHotClassCertificates
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Universal carry-prefix regimes for one-bit key classes

For the low 20 bits of ordinary addition, carry zero is always attainable.
Carry one is attainable exactly when the low key prefix is nonzero: choose
an input prefix `2^20 - keyLow`. Thus the Boolean key-class flag determines
the complete set of possible prefix carries for every 32-bit key, and
replacing a key by its representative preserves that set.

These arithmetic theorems describe `WordPrefixCarryPossible`. Relating this
prefix model and a single active S-box transition to full carry paths is
still required to establish `OneHotClassInvariant`.
-/

open Magma.OneHotKeyClasses Magma.OneHotClassCertificates

namespace Magma.OneHotCarryPrefix

private def B : Nat :=
  2 ^ 20

/-- Carry from the low 20 bits of ordinary addition.
    Only input words with 0 <= x < 2^20 are considered. -/
def PrefixCarryPossible (keyLow : Nat) (carry : Fin 2) : Prop :=
  ∃ xLow : Nat, xLow < B ∧ (xLow + keyLow) / B = carry.val

/-- A zero incoming carry can always be obtained: choose xLow = 0. -/
theorem zero_carry_possible (keyLow : Nat) (hk : keyLow < B) :
    PrefixCarryPossible keyLow 0 := by
  refine ⟨0, by norm_num [B], ?_⟩
  change (0 + keyLow) / B = 0
  exact Nat.div_eq_of_lt (by simpa only [Nat.zero_add] using hk)

/-- The high incoming carry can be produced iff the low key prefix
    is nonzero. In the forward direction this uses only the range bound;
    in the reverse direction choose xLow = B - keyLow. -/
theorem one_carry_possible_iff (keyLow : Nat) (hk : keyLow < B) :
    PrefixCarryPossible keyLow 1 ↔ keyLow ≠ 0 := by
  constructor
  · rintro ⟨xLow, hx, hcarry⟩ hzero
    subst keyLow
    have hq : xLow / B = 0 := Nat.div_eq_of_lt hx
    simp only [Nat.add_zero, hq] at hcarry
    contradiction
  · intro hnonzero
    have hpositive : 0 < keyLow := by omega
    refine ⟨B - keyLow, by omega, ?_⟩
    have hsum : B - keyLow + keyLow = B := by omega
    change (B - keyLow + keyLow) / B = 1
    rw [hsum]
    simp [B]

/-- Complete description of the set of carry-in values for a low prefix. -/
theorem prefix_carry_possible_iff
    (keyLow : Nat) (hk : keyLow < B) (carry : Fin 2) :
    PrefixCarryPossible keyLow carry ↔
      carry = 0 ∨ (carry = 1 ∧ keyLow ≠ 0) := by
  fin_cases carry
  · simp [zero_carry_possible keyLow hk]
  · simpa using (one_carry_possible_iff keyLow hk)

/-- In particular, the exact *value* of a nonzero low key prefix is
    irrelevant for the SET of achievable carry-in bits. -/
theorem prefix_carry_regime_congr
    (keyLow otherLow : Nat)
    (hk : keyLow < B) (ho : otherLow < B)
    (hzero : keyLow = 0 ↔ otherLow = 0)
    (carry : Fin 2) :
    PrefixCarryPossible keyLow carry ↔
      PrefixCarryPossible otherLow carry := by
  rw [prefix_carry_possible_iff keyLow hk carry,
      prefix_carry_possible_iff otherLow ho carry]
  constructor
  · rintro (hc | ⟨hc, hn⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨hc, fun h => hn (hzero.mpr h)⟩
  · rintro (hc | ⟨hc, hn⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨hc, fun h => hn (hzero.mp h)⟩

/-- Low 20 bits of a word interpreted as an unsigned natural number. -/
def keyLow20 (k : V 32) : Nat := k.toNat % B

theorem keyLow20_lt (k : V 32) : keyLow20 k < B := by exact Nat.mod_lt _ (by norm_num [B])

/-- The mathematical carry regime, for a complete Magma key. -/
def WordPrefixCarryPossible (k : V 32) (carry : Fin 2) : Prop :=
  PrefixCarryPossible (keyLow20 k) carry

/-- The previously introduced Bool flag is precisely the nonzero-prefix
    test. Keep this simple lemma separate from expensive carry DP. -/
theorem canCarryIntoNibble5_iff (k : V 32) :
    canCarryIntoNibble5 k = true ↔ keyLow20 k ≠ 0 := by
  unfold canCarryIntoNibble5 keyLow20 B
  simp

/-- Universal result for ANY two 32-bit keys with the same carry flag.
    This is the prefix half of the key-class invariant. -/
theorem prefix_carry_same_class (k k' : V 32)
    (hclass : canCarryIntoNibble5 k = canCarryIntoNibble5 k')
    (carry : Fin 2) :
    WordPrefixCarryPossible k carry ↔
      WordPrefixCarryPossible k' carry := by
  apply prefix_carry_regime_congr
    (keyLow20 k) (keyLow20 k')
    (keyLow20_lt k) (keyLow20_lt k')
  have hflags : (keyLow20 k ≠ 0) ↔ (keyLow20 k' ≠ 0) := by
    rw [← canCarryIntoNibble5_iff, ← canCarryIntoNibble5_iff]
    rw [hclass]
  constructor
  · intro hkzero
    by_contra hk'nonzero
    exact (hflags.mpr hk'nonzero) (hkzero)
  · intro hk'zero
    by_contra hknonzero
    exact (hflags.mp hknonzero) hk'zero

/-- Replacing a key with its 32-class representative preserves ALL
    possible incoming carries at the active nibble (not merely examples). -/
theorem representative_preserves_prefix_carries (k : V 32) (carry : Fin 2) :
    WordPrefixCarryPossible k carry ↔
      WordPrefixCarryPossible
        (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k))
        carry := by
  apply prefix_carry_same_class
  exact (representativeKey_has_class
    (keyNibble5 k) (canCarryIntoNibble5 k)).2.symm

end Magma.OneHotCarryPrefix
