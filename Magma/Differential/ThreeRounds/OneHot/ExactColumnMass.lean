module

public import Magma.Differential.ThreeRounds.OneHot.ThreeRoundColumns
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact one-bit three-round column masses

The sum over the left input difference of a zero-left three-round column
is `2^32` times the second-round DDT count. The original eight-step carry
DP computes this count exactly for every key and one-bit right output,
independently of the first and third round keys.

Support classes do not determine multiplicities: keys one and two have
the same local support class but DDT counts 512 and 1024 at bit 20.
Their total three-round column masses are therefore `2^41` and `2^42`.
The two concrete counts are checked by Lean's kernel using the carry DP.
-/

open scoped BigOperators

namespace Magma.OneHotExactColumnMass

open Magma.CarryAutomaton
open Magma.OneHotTraceSplit5
open Magma.OneHotKeyClasses
open Magma.OneHotThreeRoundColumns
open Magma.MultiRoundDDT

/-! ## 1. An executable, exact DP for every one-hot input difference -/

/-- Number of accepted paths through the genuine eight S-box/carry steps.
    Its target has just nibble 5 equal to 2, since rotating 2^21 left
    by 11 bits yields the requested XOR output difference 1. -/
def oneHotDPCount (k : V 32) (j : Fin 32) : Nat :=
  carryDPCount (wordDigits k) (wordDigits (bitOutput j)) oneHotTargetDigits

private theorem rotated_target_one : rot11 (0x00200000#32) = (1#32) := by decide

/-- THE ACTUAL g[k] DIFFERENTIAL COUNT is exactly the small-DP count.
    In particular, this equation is not merely a comparison of supports. -/
theorem oneHotDDT_eq_dp (k : V 32) (j : Fin 32) :
    xorDDT_g k (bitOutput j) (1#32) = oneHotDPCount k j := by
  calc
    xorDDT_g k (bitOutput j) (1#32) =
        carryMatrixCount (wordDigits k) (wordDigits (bitOutput j))
          (wordDigits (0x00200000#32)) := by
            simpa only [rotated_target_one] using
              (xorDDT_g_eq_carryMatrixCount
                k (bitOutput j) (0x00200000#32))
    _ = carryDPCount (wordDigits k) (wordDigits (bitOutput j))
          (wordDigits (0x00200000#32)) :=
            (carryDPCount_eq_carryMatrixCount _ _ _).symm
    _ = oneHotDPCount k j := by
      simp only [oneHotDPCount, wordDigits_oneHot_output]

private theorem card_word : Fintype.card (V 32) = 2 ^ 32 := by
  calc
    Fintype.card (V 32) = FinEnum.card (V 32) := (FinEnum.card_eq_fintypeCard).symm
    _ = 2 ^ 32 := FinEnum.card_bitVec 32

/-! ## 2. Exact three-round column masses for ALL round keys -/

/-- Exact multiplicity of an entire column: independent of k0 and k2,
    and computable from only eight small carry matrices for k1. -/
theorem oneHot_column_mass_dp
    (k₀ k₁ k₂ : V 32) (j : Fin 32) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j)) =
      2 ^ 32 * oneHotDPCount k₁ j := by
  rw [zeroLeft_row_mass, card_word, oneHotDDT_eq_dp]

/-- The DP returns a positive count exactly at the already established
    key-class-supported bit positions. This is a theorem for every key,
    not just for representatives of the 32 support classes. -/
theorem oneHotDPCount_pos_iff_class (k : V 32) (j : Fin 32) :
    0 < oneHotDPCount k j ↔ classAllowsBit k j := by
  simpa only [oneHotDDT_eq_dp] using
    (g_oneHot_positive_iff_class k j)

/-- Positive total column mass means precisely nonempty support. -/
theorem oneHot_column_mass_pos_iff_class
    (k₀ k₁ k₂ : V 32) (j : Fin 32) :
    0 < (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j)) ↔
      classAllowsBit k₁ j := by
  rw [oneHot_column_mass_dp]
  constructor
  · intro hm
    have hp : 0 < oneHotDPCount k₁ j := by
      by_contra hn
      have hz : oneHotDPCount k₁ j = 0 := Nat.eq_zero_of_not_pos hn
      simp [hz] at hm
    exact (oneHotDPCount_pos_iff_class k₁ j).mp hp
  · intro hc
    exact Nat.mul_pos (by norm_num)
      ((oneHotDPCount_pos_iff_class k₁ j).mpr hc)

/-- Changing either outer key cannot alter the exact column mass. -/
theorem oneHot_column_mass_outer_key_independent
    (k₀ k₀' k₁ k₂ k₂' : V 32) (j : Fin 32) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j)) =
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀' k₁ k₂')
        (aL, 1#32) (0#32, bitOutput j)) := by
  rw [oneHot_column_mass_dp, oneHot_column_mass_dp]

/-! ## 3. Numeric counterexample: same SUPPORT class, distinct MASSES -/

/-- A 4-state, eight-digit calculation, NOT a 2^32-word enumeration. -/
theorem oneHotDP_key1_bit20 :
    oneHotDPCount (1#32) (20 : Fin 32) = 512 := by
  decide

/-- Doubling the lowest key value doubles this small DDT entry. -/
theorem oneHotDP_key2_bit20 :
    oneHotDPCount (2#32) (20 : Fin 32) = 1024 := by
  decide

/-- Exact total three-round column mass for second-round key 1. -/
theorem key1_bit20_column_mass (k₀ k₂ : V 32) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (1#32) k₂)
        (aL, 1#32) (0#32, bitOutput (20 : Fin 32))) =
      2 ^ 41 := by
  rw [oneHot_column_mass_dp, oneHotDP_key1_bit20]
  norm_num

/-- Exact mass for the same column with second-round key 2. -/
theorem key2_bit20_column_mass (k₀ k₂ : V 32) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (2#32) k₂)
        (aL, 1#32) (0#32, bitOutput (20 : Fin 32))) =
      2 ^ 42 := by
  rw [oneHot_column_mass_dp, oneHotDP_key2_bit20]
  norm_num

/-- The already proved 32-class invariant is a SUPPORT classification,
    not a statement that DDT counts within one class are equal.
    Here the two keys have identical (q,carry-regime) but distinct exact
    three-round masses for any outer keys. -/
theorem same_support_class_different_mass (k₀ k₂ : V 32) :
    keyNibble5 (1#32) = keyNibble5 (2#32) ∧
    canCarryIntoNibble5 (1#32) = canCarryIntoNibble5 (2#32) ∧
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (1#32) k₂)
        (aL, 1#32) (0#32, bitOutput (20 : Fin 32))) ≠
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (2#32) k₂)
        (aL, 1#32) (0#32, bitOutput (20 : Fin 32))) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [key1_bit20_column_mass, key2_bit20_column_mass]
  norm_num

end Magma.OneHotExactColumnMass
