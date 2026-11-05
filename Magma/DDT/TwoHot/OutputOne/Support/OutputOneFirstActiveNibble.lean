module

public import Magma.DDT.OneHot.Support.ActiveNibbleNecessary
import all Init.Data.Range.Basic
import Magma.Differential.Core.MultiRoundDDT

@[expose] public section

/-!
Magma / two-hot input differences -> output difference 1.

First module in the next research branch. It *uses* the existing general
first-active-nibble soundness theorem; it does not search 2^32 inputs.

For a two-hot word with input bit positions i<j, the FIRST active input
nibble is i/4. The unique nonzero output nibble of the pre-rotation
output difference corresponding to the bit vector 1#32 is nibble 5.
Hence DDT_g k (2^i XOR 2^j) 1 = 0 whenever i/4 != 5.

Of C(32,2)=496 two-hot input differences, only 38 pass this necessary
condition. The other 458 are universal zeros, for EVERY 32-bit round key.
This also proves empty three-round zero-left columns for these bR values
with aR = 1, regardless of all three round keys.

The remaining 38 are NOT claimed positive. Their detailed carry analysis
is the next step: 6 pairs inside nibble 5, 32 pairs crossing to higher
nibbles. The latter can be narrowed further using later silent nibbles.

-/

namespace Magma.TwoHotOutputOneFirstActive

open Magma
open Magma.CarryAutomaton
open Magma.OneHotActiveNibbleNecessary
open Magma.MultiRoundDDT

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

/-- The input XOR difference with bits `i` and `j` flipped. -/
def twoHot (i j : Fin 32) : Word :=
  xor (BitVec.ofNat 32 (2 ^ i.val)) (BitVec.ofNat 32 (2 ^ j.val))

/-- The XOR representation agrees with the ordinary two-bit
    differences already used by `BatchSearch.twoBitDifferences32`.
    The proof checks at most 32×32 index pairs. -/
theorem twoHot_eq_sum (i j : Fin 32) (hij : i.val < j.val) :
    twoHot i j = BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) := by
  revert i j
  decide +kernel

/-- The target difference before the fixed eleven-bit output rotation. -/
private def preOutputOne : Word := 0x00200000#32

private theorem preOutputOne_rot : rot11 preOutputOne = (1#32) := by decide +kernel

/-- Only nibble five of the unrotated output-one word is nonzero. -/
private theorem preOutputOne_silent (u : Fin 8) (hu : u.val ≠ 5) :
    wordDigits preOutputOne u = 0 := by
  revert u
  decide +kernel

/-- Digit of an individual one-hot input word is zero in any other
    nibble. This duplicates a small PRIVATE fact of the old one-hot
    module instead of modifying its public interface. -/
private theorem oneBit_other_digit_zero (j : Fin 32) (u : Fin 8)
    (hu : u.val ≠ j.val / 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) u = 0 := by
  revert j u
  decide +kernel

private theorem digit_xor_zero : xorDigit (0 : Fin 16) 0 = 0 := by decide +kernel

/-- Every nibble below the least changed bit of a two-hot input is zero. -/
theorem twoHot_lower_digits_zero
    (i j : Fin 32) (hij : i.val < j.val) (u : Fin 8)
    (hu : u.val < i.val / 4) :
    wordDigits (twoHot i j) u = 0 := by
  have h0 : u.val ≠ i.val / 4 := by omega
  have h1 : u.val ≠ j.val / 4 := by omega
  unfold twoHot
  rw [wordDigits_xor,
    oneBit_other_digit_zero i u h0,
    oneBit_other_digit_zero j u h1]
  exact digit_xor_zero

/-- The first active nibble cannot cancel: two distinct input bit
    positions always induce a nonzero digit at the nibble containing
    the smaller position. This is a finite statement about at most
    32*32 index pairs, NOT an enumeration of 32-bit inputs. -/
theorem twoHot_first_digit_nonzero
    (i j : Fin 32) (hij : i.val < j.val) :
    wordDigits (twoHot i j)
      (⟨i.val / 4, by omega⟩ : Fin 8) ≠ 0 := by
  revert i j
  decide +kernel

/-- GENERAL necessary condition for output difference one. It applies
    to any nonzero input difference having a specified first active
    nibble, not just to two-hot inputs. -/
theorem output_one_zero_of_first_active_not_five
    (k a : Word) (u : Fin 8)
    (hlow : ∀ v : Fin 8, v.val < u.val → wordDigits a v = 0)
    (ha : wordDigits a u ≠ 0)
    (hu : u.val ≠ 5) :
    xorDDT_g k a (1#32) = 0 := by
  have hz := xorDDT_zero_if_first_active_nibble_is_silent
    k a preOutputOne u hlow ha (preOutputOne_silent u hu)
  rw [preOutputOne_rot] at hz
  exact hz

/-- A two-bit input difference with its FIRST active nibble other than
    five has zero DDT at output difference one, for ANY round key. -/
theorem twoHot_output_one_zero_of_not_middle
    (k : Word) (i j : Fin 32)
    (hij : i.val < j.val) (hi : i.val / 4 ≠ 5) :
    xorDDT_g k (twoHot i j) (1#32) = 0 := by
  let u : Fin 8 := ⟨i.val / 4, by omega⟩
  have hlow : ∀ v : Fin 8, v.val < u.val →
      wordDigits (twoHot i j) v = 0 := by
    intro v hv
    exact twoHot_lower_digits_zero i j hij v (by simpa [u] using hv)
  have hactive : wordDigits (twoHot i j) u ≠ 0 :=
    twoHot_first_digit_nonzero i j hij
  apply output_one_zero_of_first_active_not_five
    k (twoHot i j) u hlow hactive
  simpa [u] using hi

/-- Relevant candidates for output difference one. -/
def relevantPair (p : PairBits) : Prop :=
  p.1.val < p.2.val ∧ p.1.val / 4 = 5

instance (p : PairBits) : Decidable (relevantPair p) :=
  inferInstanceAs (Decidable (p.1.val < p.2.val ∧ p.1.val / 4 = 5))

def excludedPair (p : PairBits) : Prop :=
  p.1.val < p.2.val ∧ p.1.val / 4 ≠ 5

instance (p : PairBits) : Decidable (excludedPair p) :=
  inferInstanceAs (Decidable (p.1.val < p.2.val ∧ p.1.val / 4 ≠ 5))

/-- Every relevant pair has the first bit in positions 20,21,22,23. -/
theorem relevantPair_iff_middle (p : PairBits) :
    relevantPair p ↔
      p.1.val < p.2.val ∧ 20 ≤ p.1.val ∧ p.1.val < 24 := by
  simp only [relevantPair]
  omega

/-- C(32,2) pairs of distinct input bit indices. -/
theorem all_twoHot_index_pairs_card :
    ((Finset.univ : Finset PairBits).filter
      (fun p => p.1.val < p.2.val)).card = 496 := by
  decide +kernel

/-- Only six within-nibble-5 pairs plus 32 across-nibble pairs remain. -/
theorem relevant_pairs_card :
    ((Finset.univ : Finset PairBits).filter relevantPair).card = 38 := by
  decide +kernel

theorem relevant_same_nibble_card :
    ((Finset.univ : Finset PairBits).filter (fun p => relevantPair p ∧ p.2.val < 24)).card = 6 := by
  decide +kernel

theorem relevant_cross_nibble_card :
    ((Finset.univ : Finset PairBits).filter (fun p => relevantPair p ∧ 24 ≤ p.2.val)).card =
      32 := by
  decide +kernel

/-- A full 458 out of 496 two-hot input/output-one transitions are
    impossible for EVERY 32-bit round key, without any DDT search. -/
theorem excluded_pairs_card :
    ((Finset.univ : Finset PairBits).filter excludedPair).card = 458 := by
  decide +kernel

theorem excluded_pairs_sound (k : Word) (p : PairBits) (hp : excludedPair p) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) = 0 :=
  twoHot_output_one_zero_of_not_middle k p.1 p.2 hp.1 hp.2

/-- Immediate three-round consequence: all zero-left output columns
    whose right output difference belongs to the 458 excluded two-hot
    inputs are identically zero (with right INPUT difference 1). -/
theorem three_round_zeroLeft_column_empty
    (k₀ k₁ k₂ aL : Word) (i j : Fin 32)
    (hij : i.val < j.val) (hi : i.val / 4 ≠ 5) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, twoHot i j) = 0 := by
  have hz := twoHot_output_one_zero_of_not_middle k₁ i j hij hi
  exact (zeroLeft_column_empty_iff k₀ k₁ k₂ (1#32) (twoHot i j)).mpr hz aL

end Magma.TwoHotOutputOneFirstActive
