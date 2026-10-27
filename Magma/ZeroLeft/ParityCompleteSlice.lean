module

public import Magma.ZeroLeft.KeyParity
public import Magma.ZeroLeft.OddKey
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Complete parity-based description of the zero-left three-round slice

Fix right input difference one and left output difference zero; all three
round keys and the other two differences remain arbitrary. `parityRowCount`
and `parityRowSupport` combine the complete eight-entry even-key row with
the certified 77-entry odd-key row in actual output coordinates.

Every coefficient is its parity-selected first-round count times the genuine
second-round DDT factor. A column has exactly zero positive entries when
that second factor vanishes, otherwise eight for an even first key and 77
for an odd first key. Positive supports are the corresponding XOR translates.

The third key is irrelevant. At one-bit right outputs in positions 20 through
23, the second factor also has the proved affine coefficient-mask formula.
All support and count arguments are symbolic.
-/

namespace Magma.ZeroLeftParityCompleteSlice

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.ZeroLeftColumnTransport
open Magma.ZeroLeftEightEntries
open Magma.UnitInputParityReduction
open Magma.OddUnitInput77
open Magma.OneHotExactCoefficientMasks
open Magma.OneHotKeyClasses

/-- The one-round exact DDT reference row, selected by the parity
    of its round key. This is a *count*, not a Boolean prediction. -/
def parityRowCount (k d : (V 32)) : Nat :=
  if k.toNat % 2 = 0 then
    if d ∈ eightOffsets then 2 ^ 29 else 0
  else
    oddReferenceCount d

/-- The corresponding exact support in actual post-rotation coordinates. -/
def parityRowSupport (k : (V 32)) : Finset (V 32) :=
  if k.toNat % 2 = 0 then eightOffsets else oddOutputSupport

/-- UNCONDITIONAL exact one-round DDT, valid for every 32-bit key
    and every possible 32-bit output difference. -/
theorem one_round_unit_exact (k d : (V 32)) :
    xorDDT_g k (1#32) d = parityRowCount k d := by
  by_cases hk : k.toNat % 2 = 0
  · simpa only [parityRowCount, hk, ite_true] using
      (evenKey_first_row_exact k d hk)
  · have hodd : k.toNat % 2 = 1 := by omega
    simpa only [parityRowCount, hk, ite_false] using
      (odd_key_complete_DDT k d hodd)

/-- The list of positive offsets is likewise valid for *every* k. -/
theorem one_round_unit_support_exact (k : (V 32)) :
    firstRoundSupport k (1#32) = parityRowSupport k := by
  by_cases hk : k.toNat % 2 = 0
  · simpa only [parityRowSupport, hk, ite_true] using
      (evenKey_first_support_exact k hk)
  · have hodd : k.toNat % 2 = 1 := by omega
    have hsupport :
        firstRoundSupport k (1#32) = oddOutputSupport := by
      classical
      ext d
      simp only [firstRoundSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact odd_key_positive_iff_support k d hodd
    simpa only [parityRowSupport, hk, ite_false] using hsupport

/-- Exact support size of the first-round row: always 8 or 77. -/
theorem one_round_unit_support_card (k : (V 32)) :
    (firstRoundSupport k (1#32)).card =
      if k.toNat % 2 = 0 then 8 else 77 := by
  rw [one_round_unit_support_exact]
  by_cases hk : k.toNat % 2 = 0
  · simpa only [parityRowSupport, hk, ite_true] using eightOffsets_card
  · simpa only [parityRowSupport, hk, ite_false] using odd_output_support_card

/-- MAIN THEOREM: every individual three-round coefficient in the
    zero-left slice with aR=1, without restrictions on any round key.

    The first factor is an explicit 8-entry or 77-entry reference row;
    the second factor is the genuine (and independently computable)
    one-round DDT at the arbitrary second key. -/
theorem every_three_round_entry_exact
    (k₀ k₁ k₂ aL bR : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR) =
      parityRowCount k₀ (xor bR aL) *
        xorDDT_g k₁ bR (1#32) := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      one_round_unit_exact]

/-- Exact criterion for one specific coefficient to be nonzero. -/
theorem every_three_round_entry_positive_iff
    (k₀ k₁ k₂ aL bR : (V 32)) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR) ↔
      xor bR aL ∈ parityRowSupport k₀ ∧
        0 < xorDDT_g k₁ bR (1#32) := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  constructor
  · intro hp
    have h0 : 0 < xorDDT_g k₀ (1#32) (xor bR aL) :=
      Nat.pos_of_mul_pos_right hp
    have h1 : 0 < xorDDT_g k₁ bR (1#32) :=
      Nat.pos_of_mul_pos_left hp
    rw [← one_round_unit_support_exact k₀]
    exact ⟨(Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩), h1⟩
  · rintro ⟨hoffset, h1⟩
    rw [← one_round_unit_support_exact k₀] at hoffset
    have h0 : 0 < xorDDT_g k₀ (1#32) (xor bR aL) :=
      (Finset.mem_filter.mp hoffset).2
    exact Nat.mul_pos h0 h1

/-- Exact SET of all positive coefficients of an arbitrary column.
    The empty case and both key-parity cases are handled uniformly. -/
theorem every_three_round_column_support
    (k₀ k₁ k₂ bR : (V 32)) :
    leftColumnSupport k₀ k₁ k₂ (1#32) bR =
      if xorDDT_g k₁ bR (1#32) = 0 then ∅
      else (parityRowSupport k₀).image (fun d => xor bR d) := by
  by_cases hC : xorDDT_g k₁ bR (1#32) = 0
  · simpa only [hC, ite_true] using
      (leftColumnSupport_empty_of_second_zero
        k₀ k₁ k₂ (1#32) bR hC)
  · have hpos : 0 < xorDDT_g k₁ bR (1#32) := by omega
    rw [leftColumnSupport_eq_image_of_pos
      k₀ k₁ k₂ (1#32) bR hpos,
      one_round_unit_support_exact]
    simp only [hC, ite_false]

/-- MAIN CARDINALITY THEOREM. An entire column has EXACTLY
    0, 8, or 77 nonzero DDT coefficients, and these are the only
    possibilities for arbitrary k0,k1,k2,bR (with aR=1).

    In a nonempty column: 8 if k0 is even, 77 if k0 is odd. -/
theorem every_three_round_column_card
    (k₀ k₁ k₂ bR : (V 32)) :
    (leftColumnSupport k₀ k₁ k₂ (1#32) bR).card =
      if xorDDT_g k₁ bR (1#32) = 0 then 0
      else if k₀.toNat % 2 = 0 then 8 else 77 := by
  by_cases hC : xorDDT_g k₁ bR (1#32) = 0
  · rw [leftColumnSupport_empty_of_second_zero
      k₀ k₁ k₂ (1#32) bR hC]
    simp only [Finset.card_empty, hC, ite_true]
  · have hpos : 0 < xorDDT_g k₁ bR (1#32) := by omega
    rw [leftColumnSupport_card_of_pos
      k₀ k₁ k₂ (1#32) bR hpos,
      one_round_unit_support_card]
    simp only [hC, ite_false]

/-- Distinct values of the third key do not change this slice at all. -/
theorem third_key_irrelevant
    (k₀ k₁ k₂ k₂' aL bR : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) =
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂')
      (aL, 1#32) (0#32, bR) := by
  rw [every_three_round_entry_exact,
      every_three_round_entry_exact]

/-- The one-hot second-round DDT is explicitly affine in the lower
    20 key bits. This gives a closed formula for EACH corresponding
    three-round coefficient, for both parities of the first key. -/
theorem every_onehot_three_round_entry_exact
    (k₀ k₁ k₂ aL : (V 32)) (r : Fin 4) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32)
        (0#32, BitVec.ofNat 32 (2 ^ (20 + r.val))) =
      parityRowCount k₀
          (xor (BitVec.ofNat 32 (2 ^ (20 + r.val))) aL) *
        (2 ^ 9 *
          ((2 ^ 20 - k₁.toNat % (2 ^ 20)) *
              coefficientBit (keyNibble5 k₁) r +
            (k₁.toNat % (2 ^ 20)) *
              coefficientBit (nextNibble (keyNibble5 k₁)) r)) := by
  rw [every_three_round_entry_exact,
      oneHot_g_DDT_exact_mask]

end Magma.ZeroLeftParityCompleteSlice
