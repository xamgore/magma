module

public import Magma.DDT.OneHot.Mechanics.QuantitativeTraceFactorization
import Mathlib.Tactic.Ring
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact coefficient masks for one-bit DDT counts

The 128 active-nibble multiplicities are zero or two. Sixteen explicit
four-bit masks encode them: carry zero selects the mask of key nibble `q`,
and carry one selects the mask of `(q + 1) mod 16`. The local table is
checked against the original S-box carry transition by Lean's kernel.

Substitution into the quantitative trace factorization gives the original
one-round DDT as `2^9 * ((2^20 - K) * e(q,r) + K * e(q+1,r))`, where `K`
is the low twenty key bits and `e` extracts a coefficient-mask bit.
The corresponding three-round column mass has prefactor `2^41`.
The four possible pairs of mask bits yield zero, linear growth, linear
decrease, or the constant count `2^29`, for every key at bits 20 through 23.
-/

open scoped BigOperators

namespace Magma.OneHotExactCoefficientMasks

open Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotLinearPrefixMass
open Magma.OneHotKeyClasses
open Magma.OneHotQuantitativeTraceFactorization
open Magma.OneHotThreeRoundColumns

private abbrev B : Nat :=
  2 ^ 20

/-! ## 1. The 16 explicit four-bit coefficient masks. -/

/-- The r-th bit records whether the active S-box has multiplicity two
    for key nibble q and incoming carry zero. -/
def coefficientMask (q : Fin 16) : Nat :=
  match q.val with
  | 0 => 0x8
  | 1 => 0xD
  | 2 => 0xE
  | 3 => 0xF
  | 4 => 0xC
  | 5 => 0x9
  | 6 => 0xA
  | 7 => 0x3
  | 8 => 0x0
  | 9 => 0x5
  | 10 => 0x6
  | 11 => 0x7
  | 12 => 0x4
  | 13 => 0x1
  | 14 => 0x2
  | _ => 0xB

/-- A coefficient is a single bit extracted from a four-bit mask. -/
def coefficientBit (q : Fin 16) (r : Fin 4) : Nat :=
  coefficientMask q / 2 ^ r.val % 2

/-- The next key nibble, wrapping 15 to 0. -/
def nextNibble (q : Fin 16) : Fin 16 := Fin.ofNat 16 (q.val + 1)

/-- These masks are all in the nibble range. -/
theorem coefficientMask_lt (q : Fin 16) : coefficientMask q < 16 := by
  fin_cases q <;> decide

/-- Every four-bit support mask occurs exactly once.
    In key-nibble order the masks are
    `[8, 13, 14, 15, 12, 9, 10, 3, 0, 5, 6, 7, 4, 1, 2, 11]`. -/
theorem coefficientMasks_nodup :
    ((List.finRange 16).map coefficientMask).Nodup := by decide

/-- A coefficient bit is necessarily zero or one. -/
theorem coefficientBit_lt_two (q : Fin 16) (r : Fin 4) :
    coefficientBit q r < 2 := by
  unfold coefficientBit
  exact Nat.mod_lt _ (by norm_num)

/-! ## 2. Full exact local S-box table: 16 × 2 × 4 combinations. -/

/-- The 64 cases with zero incoming carry, checked against original
    sboxCarryStep and the RFC pi_5 substitution, not a new S-box model. -/
theorem activeMultiplicity_zero_exact (q : Fin 16) (r : Fin 4) :
    activeMultiplicity q 0 r = 2 * coefficientBit q r := by
  fin_cases q <;> fin_cases r <;> decide

/-- The 64 cases with incoming carry one are just the same table shifted
    by one in the key nibble (including wraparound from 15 to zero). -/
theorem activeMultiplicity_one_exact (q : Fin 16) (r : Fin 4) :
    activeMultiplicity q 1 r = 2 * coefficientBit (nextNibble q) r := by
  fin_cases q <;> fin_cases r <;> decide

/-- All 128 active multiplicities are exactly zero or two. -/
theorem activeMultiplicity_exact (q : Fin 16) (c : Fin 2) (r : Fin 4) :
    activeMultiplicity q c r =
      2 * coefficientBit (if c = 0 then q else nextNibble q) r := by
  fin_cases c
  · simpa using activeMultiplicity_zero_exact q r
  · simpa using activeMultiplicity_one_exact q r

/-- Numerically, adding a carry of 1 to q is equivalent to increasing
    the key nibble by one, for the multiplicity of this target. -/
theorem activeMultiplicity_carry_shift (q : Fin 16) (r : Fin 4) :
    activeMultiplicity q 1 r = activeMultiplicity (nextNibble q) 0 r := by
  rw [activeMultiplicity_one_exact, activeMultiplicity_zero_exact]

/-! ## 3. The simplified REAL one-round and three-round formulas. -/

/-- An analytic closed form involving TWO MASK BITS instead of 128
    unrelated local counts. For every 32-bit key, no extra hypothesis. -/
theorem oneHot_g_DDT_exact_mask (k : V 32) (r : Fin 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 9 *
        ((B - k.toNat % B) * coefficientBit (keyNibble5 k) r +
          (k.toNat % B) * coefficientBit (nextNibble (keyNibble5 k)) r) := by
  rw [oneHot_g_DDT_affine,
    activeMultiplicity_zero_exact, activeMultiplicity_one_exact]
  norm_num
  ring

/-- Exact mass of an entire three-round zero-left one-hot column,
    regardless of the first and third round keys. -/
theorem oneHot_three_round_mass_exact_mask
    (k₀ k₁ k₂ : V 32) (r : Fin 4) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32,
          bitOutput (⟨20 + r.val, by omega⟩ : Fin 32))) =
      2 ^ 41 *
        ((B - k₁.toNat % B) * coefficientBit (keyNibble5 k₁) r +
          (k₁.toNat % B) * coefficientBit (nextNibble (keyNibble5 k₁)) r) := by
  rw [oneHot_three_round_column_mass_affine,
    activeMultiplicity_zero_exact, activeMultiplicity_one_exact]
  norm_num
  ring

/-- All such one-round DDT entries are divisible by 512. -/
theorem oneHot_g_DDT_divisible_512 (k : V 32) (r : Fin 4) :
    2 ^ 9 ∣ xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) := by
  rw [oneHot_g_DDT_exact_mask]
  exact ⟨_, rfl⟩

/-- All such three-round column masses are divisible by 2^41. -/
theorem oneHot_three_round_mass_divisible (k₀ k₁ k₂ : V 32)
    (r : Fin 4) :
    2 ^ 41 ∣
      (∑ aL : V 32,
        xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
          (aL, 1#32) (0#32,
            bitOutput (⟨20 + r.val, by omega⟩ : Fin 32))) := by
  rw [oneHot_three_round_mass_exact_mask]
  exact ⟨_, rfl⟩

/-! ## 4. Four precise affine regimes, proved for the original DDT. -/

/-- Neither incoming-carry regime works: the DDT is zero. -/
theorem DDT_if_both_bits_zero (k : V 32) (r : Fin 4)
    (h₀ : coefficientBit (keyNibble5 k) r = 0)
    (h₁ : coefficientBit (nextNibble (keyNibble5 k)) r = 0) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) = 0 := by
  rw [oneHot_g_DDT_exact_mask, h₀, h₁]
  simp

/-- Only incoming carry one works: linear growth from zero. -/
theorem DDT_if_only_carry_one (k : V 32) (r : Fin 4)
    (h₀ : coefficientBit (keyNibble5 k) r = 0)
    (h₁ : coefficientBit (nextNibble (keyNibble5 k)) r = 1) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 9 * (k.toNat % B) := by
  rw [oneHot_g_DDT_exact_mask, h₀, h₁]
  simp

/-- Only incoming carry zero works: linear decrease with low key K. -/
theorem DDT_if_only_carry_zero (k : V 32) (r : Fin 4)
    (h₀ : coefficientBit (keyNibble5 k) r = 1)
    (h₁ : coefficientBit (nextNibble (keyNibble5 k)) r = 0) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 9 * (B - k.toNat % B) := by
  rw [oneHot_g_DDT_exact_mask, h₀, h₁]
  simp

/-- Both carry regimes work: the DDT is constant, 2^29. -/
theorem DDT_if_both_bits_one (k : V 32) (r : Fin 4)
    (h₀ : coefficientBit (keyNibble5 k) r = 1)
    (h₁ : coefficientBit (nextNibble (keyNibble5 k)) r = 1) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 29 := by
  rw [oneHot_g_DDT_exact_mask, h₀, h₁]
  have hK : k.toNat % B ≤ B :=
    Nat.le_of_lt (Nat.mod_lt _ (by norm_num [B]))
  simp only [mul_one]
  rw [Nat.sub_add_cancel hK]
  norm_num [B]

/-- A salient class: nibble 8, with input bit 20 or 22. The exact DDT
    is 512 times the low twenty key bits, for arbitrary upper key bits. -/
theorem nibble8_bit20_exact (k : V 32) (hq : keyNibble5 k = 8) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ 20)) (1#32) =
      2 ^ 9 * (k.toNat % B) := by
  have h₀ : coefficientBit (keyNibble5 k) 0 = 0 := by rw [hq]; decide
  have h₁ : coefficientBit (nextNibble (keyNibble5 k)) 0 = 1 := by
    rw [hq]; decide
  simpa using DDT_if_only_carry_one k 0 h₀ h₁

theorem nibble8_bit22_exact (k : V 32) (hq : keyNibble5 k = 8) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ 22)) (1#32) = 2 ^ 9 * (k.toNat % B) := by
  have h₀ : coefficientBit (keyNibble5 k) 2 = 0 := by
    rw [hq]; decide
  have h₁ : coefficientBit (nextNibble (keyNibble5 k)) 2 = 1 := by
    rw [hq]; decide
  simpa using DDT_if_only_carry_one k 2 h₀ h₁

end Magma.OneHotExactCoefficientMasks
