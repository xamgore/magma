module

public import Magma.DDT.OneHot.Support.FixedKeySupport72
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact incoming-carry regimes at every nibble

The arithmetic prefix formula characterizes the actual addition carry:
zero is always reachable, and one is reachable exactly when the lower
key prefix is nonzero. This criterion holds at all eight nibble positions.

The exact flag removes the fictitious carry-one states admitted by the
conservative flag at higher nibbles. The resulting local support count
is defined and checked on concrete keys; equality with the real fixed-key
DDT support is a separate completeness statement.
-/

namespace Magma.OneHotExactCarryRegimes

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotFixedKeySupport72

private abbrev Word :=
  V 32

/-- Base of the prefix ending before nibble i. -/
def nibbleBase (i : Fin 8) : Nat := 16 ^ i.val

private theorem nibbleBase_pos (i : Fin 8) : 0 < nibbleBase i := by simp [nibbleBase]

private theorem nibbleBase_le_word (i : Fin 8) : nibbleBase i ≤ 2 ^ 32 := by
  fin_cases i <;> norm_num [nibbleBase]

/-- The EXACT condition for a carry-one to be reachable is that the
    lower key prefix is nonzero, for all eight nibble indices. -/
def exactCarryFlag (k : Word) (i : Fin 8) : Bool :=
  decide (k.toNat % nibbleBase i ≠ 0)

/-- This arithmetic formula is a semantic property of the actual
    eight-digit carry recurrence, not a key-class heuristic. -/
theorem incomingCarry_prefix_formula (k x : Word) (i : Fin 8) :
    (incomingCarry (wordDigitStream x) (wordDigitStream k) i.val).val =
      ((x.toNat % nibbleBase i) + (k.toNat % nibbleBase i)) /
        nibbleBase i := by
  let c := incomingCarry (wordDigitStream x) (wordDigitStream k) i.val
  let R := digitPrefixValue
    (addedDigits (wordDigitStream x) (wordDigitStream k)) i.val
  let B := nibbleBase i
  have hB : 0 < B := nibbleBase_pos i
  have hR : R < B := digitPrefixValue_lt _ _
  have hsum :
      x.toNat % B + k.toNat % B = R + B * c.val := by
    have h := digitPrefixValue_add_carry
      (wordDigitStream x) (wordDigitStream k) i.val
    rw [digitPrefixValue_wordDigitStream,
      digitPrefixValue_wordDigitStream] at h
    exact h
  change c.val = _
  calc
    c.val = R / B + c.val := by rw [Nat.div_eq_of_lt hR]; simp
    _ = (R + B * c.val) / B :=
      (Nat.add_mul_div_left R c.val hB).symm
    _ = (x.toNat % B + k.toNat % B) / B := by rw [hsum]

/-- An elementary binary-carry classification for any positive base. -/
private theorem arithmetic_prefix_carries
    (B K : Nat) (hB : 0 < B) (hK : K < B) (c : Fin 2) :
    (∃ X : Nat, X < B ∧ (X + K) / B = c.val) ↔
      c = 0 ∨ (c = 1 ∧ K ≠ 0) := by
  fin_cases c
  · constructor
    · intro _; exact Or.inl rfl
    · intro _
      refine ⟨0, hB, ?_⟩
      simpa using (Nat.div_eq_of_lt hK)
  · constructor
    · rintro ⟨X, hX, hq⟩
      have hne : K ≠ 0 := by
        intro hz
        subst K
        have he : X / B = 0 := Nat.div_eq_of_lt hX
        simp only [Nat.add_zero, he] at hq
        contradiction
      exact Or.inr ⟨rfl, hne⟩
    · intro h
      have hne : K ≠ 0 := by
        rcases h with h | h
        · contradiction
        · exact h.2
      have hKpos : 0 < K := Nat.pos_of_ne_zero hne
      refine ⟨B - K, by omega, ?_⟩
      have hsum : B - K + K = B := by omega
      change (B - K + K) / B = 1
      rw [hsum]
      exact Nat.div_self hB

/-- An incoming carry of 0 is always reachable; a carry of 1 is
    reachable iff the key is nonzero below this nibble. This concerns
    the actual `incomingCarry` used in the round function. -/
theorem incomingCarry_reachable_iff
    (k : Word) (i : Fin 8) (c : Fin 2) :
    (∃ x : Word,
       incomingCarry (wordDigitStream x) (wordDigitStream k) i.val = c) ↔
      c = 0 ∨ (c = 1 ∧ exactCarryFlag k i = true) := by
  let B := nibbleBase i
  let K := k.toNat % B
  have hB : 0 < B := nibbleBase_pos i
  have hK : K < B := Nat.mod_lt _ hB
  have harith := arithmetic_prefix_carries B K hB hK c
  have hflag : exactCarryFlag k i = true ↔ K ≠ 0 := by
    simp [exactCarryFlag, K, B]
  constructor
  · rintro ⟨x, hc⟩
    have hv := incomingCarry_prefix_formula k x i
    rw [hc] at hv
    have hx : x.toNat % B < B := Nat.mod_lt _ hB
    have hout : c = 0 ∨ (c = 1 ∧ K ≠ 0) :=
      harith.mp ⟨x.toNat % B, hx, hv.symm⟩
    rcases hout with h | ⟨h, hn⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hflag.mpr hn⟩
  · intro h
    have h' : c = 0 ∨ (c = 1 ∧ K ≠ 0) := by
      rcases h with h | ⟨h, hf⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hflag.mp hf⟩
    obtain ⟨X, hX, hquot⟩ := harith.mpr h'
    let x : Word := BitVec.ofNat 32 X
    have hXwidth : X < 2 ^ 32 := lt_of_lt_of_le hX (nibbleBase_le_word i)
    have hxNat : x.toNat = X := by
      simp only [x, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hXwidth
    refine ⟨x, Fin.ext ?_⟩
    rw [incomingCarry_prefix_formula, hxNat]
    have hrem : X % B = X := Nat.mod_eq_of_lt hX
    rw [hrem]
    exact hquot

/-- All possible incoming carry bits are described by the exact flag. -/
theorem carry_one_reachable_iff (k : Word) (i : Fin 8) :
    (∃ x : Word,
      incomingCarry (wordDigitStream x) (wordDigitStream k) i.val = 1) ↔
    exactCarryFlag k i = true := by
  simpa using (incomingCarry_reachable_iff k i (1 : Fin 2))

theorem carry_zero_reachable (k : Word) (i : Fin 8) :
    ∃ x : Word, incomingCarry (wordDigitStream x) (wordDigitStream k) i.val = 0 := by
  exact (incomingCarry_reachable_iff k i (0 : Fin 2)).mpr (Or.inl rfl)

/-- Prefix-carry flags can be read directly from the key's low bits. -/
theorem exactCarryFlag_eq_low_prefix (k : Word) (i : Fin 8) :
    exactCarryFlag k i = true ↔ k.toNat % (16 ^ i.val) ≠ 0 := by
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- Unlike the old conservative flag, the exact flag never authorizes
    carry one above an all-zero lower key prefix. -/
theorem exactCarryFlag_zero_key (i : Fin 8) :
    exactCarryFlag (0#32) i = false := by
  simp [exactCarryFlag, nibbleBase]

/-- An executable *local* prediction. The completeness of this formula
    for the actual DDT (not just carry reachability) is the NEXT bridge. -/
def exactLocalSupportCount (k : Word) : Nat :=
  ∑ i : Fin 8,
    localPotentialCount i (wordDigits k i) (exactCarryFlag k i)

/-! Expected-value tests belong in `example` rather than a printed `#eval`.
    There is no full 2^32-word enumeration. -/

example : exactLocalSupportCount (0#32) = 59 := by decide +kernel

/-- Demonstrates why the old overapproximation cannot appear in an
    EQUALITY: it authorizes an impossible carry-one above zero prefixes. -/
example :
    (∑ i : Fin 8,
      localPotentialCount i (wordDigits (0#32) i)
        (feasibleCarryFlag (0#32) i)) = 68 := by decide +kernel

example : exactLocalSupportCount candidate72Key = 72 := by decide +kernel

end Magma.OneHotExactCarryRegimes
