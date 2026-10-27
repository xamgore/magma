module

public import Magma.CarryAutomaton
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Universal lower-nibble zeros in the one-hot XOR-DDT matrix

An input difference with a zero nibble prefix cannot create a difference
in that prefix through modular addition and the parallel S-box layer.
After undoing the final eleven-bit rotation, this gives an upper
block-triangular support constraint for the full 32-by-32 one-hot DDT,
uniformly over every round key.

Exactly 448 index pairs are excluded. The arithmetic invariant is proved
symbolically; finite checks enumerate only bit positions and their pairs.
-/

namespace Magma.OneHotUniversalLowerNibbleZeros

open Magma
open Magma.CarryAutomaton

private abbrev Word :=
  V 32

/-- `16^m = 2^(4*m)`: a nibble prefix is a binary prefix. -/
private theorem sixteen_pow_eq_two_pow (m : Nat) :
    (16 : Nat) ^ m = 2 ^ (4 * m) := by
  calc
    (16 : Nat) ^ m = (2 ^ 4) ^ m := by norm_num
    _ = 2 ^ (4 * m) := by rw [pow_mul]

/-- XOR with a word whose low `m` nibbles vanish leaves that prefix
    unchanged. No hypothesis about the key is needed. -/
private theorem xor_preserves_low_prefix
    (x d : Word) (m : Nat)
    (hd : d.toNat % 16 ^ m = 0) :
    (xor x d).toNat % 16 ^ m = x.toNat % 16 ^ m := by
  have hp := sixteen_pow_eq_two_pow m
  have hd' : d.toNat % 2 ^ (4 * m) = 0 := by
    simpa only [hp] using hd
  simp only [xor, BitVec.xor_eq, BitVec.toNat_xor]
  rw [hp, Nat.xor_mod_two_pow, hd']
  simp

/-- Modular addition preserves congruence on any nibble prefix.
    We reuse the already-proved bridge from RFC `modShift` to Nat. -/
private theorem modShift_preserves_low_prefix
    (k x y : Word) (m : Nat) (hm : m ≤ 8)
    (hxy : x.toNat % 16 ^ m = y.toNat % 16 ^ m) :
    (GProperties.modShift k x).toNat % 16 ^ m =
      (GProperties.modShift k y).toNat % 16 ^ m := by
  have hdvd : (16 : Nat) ^ m ∣ 16 ^ 8 :=
    Nat.pow_dvd_pow 16 hm
  rw [modShift_toNat_bridge, modShift_toNat_bridge,
    Nat.mod_mod_of_dvd _ hdvd, Nat.mod_mod_of_dvd _ hdvd]
  calc
    (x.toNat + k.toNat) % 16 ^ m =
        (x.toNat % 16 ^ m + k.toNat % 16 ^ m) % 16 ^ m :=
      Nat.add_mod _ _ _
    _ = (y.toNat % 16 ^ m + k.toNat % 16 ^ m) % 16 ^ m := by
      rw [hxy]
    _ = (y.toNat + k.toNat) % 16 ^ m :=
      (Nat.add_mod _ _ _).symm

/-- A prefix equality through the end of nibble `i` forces that very
    nibble to be equal, by the usual division-and-remainder rule. -/
private theorem digit_eq_of_prefix_eq
    (x y : Word) (i : Fin 8)
    (h : x.toNat % 16 ^ (i.val + 1) =
      y.toNat % 16 ^ (i.val + 1)) :
    wordDigits x i = wordDigits y i := by
  apply Fin.ext
  rw [wordDigits_val, wordDigits_val]
  have hp : (16 : Nat) ^ (i.val + 1) =
      16 ^ i.val * 16 := by simp [pow_succ]
  rw [hp] at h
  have hh := congrArg (fun z : Nat => z / 16 ^ i.val) h
  simpa only [Nat.mod_mul_right_div_self] using hh

/-- The central symbolic invariant: if no input bit in a given nibble
    prefix changes, modular addition cannot create a difference there. -/
private theorem output_nibble_equal_of_input_prefix_zero
    (k d x : Word) (i : Fin 8)
    (hd : d.toNat % 16 ^ (i.val + 1) = 0) :
    Internal.nibble (GProperties.modShift k (xor x d)) i =
      Internal.nibble (GProperties.modShift k x) i := by
  have hx := xor_preserves_low_prefix x d (i.val + 1) hd
  have hm : i.val + 1 ≤ 8 := by omega
  have hprefix := modShift_preserves_low_prefix k (xor x d) x
    (i.val + 1) hm hx
  have hdigits := digit_eq_of_prefix_eq
    (GProperties.modShift k (xor x d))
    (GProperties.modShift k x) i hprefix
  exact BitVec.toFin_injective hdigits

/-- GENERAL LOWER-NIBBLE EXCLUSION.
    This works for arbitrary input differences `d` and target words `b`.
    The target `b` is expressed BEFORE the final 11-bit rotation.
    No 32-bit input is searched or enumerated. -/
theorem xorDDT_zero_of_lower_nibble
    (k d b : Word) (i : Fin 8)
    (hd : d.toNat % 16 ^ (i.val + 1) = 0)
    (hb : wordDigits b i ≠ 0) :
    xorDDT_g k d (rot11 b) = 0 := by
  have hb' : Internal.nibble b i ≠ (0#4) := by
    intro hz
    apply hb
    change (Internal.nibble b i).toFin = 0
    rw [hz]
    decide
  rw [xorDDT_g_eq_nibbles]
  unfold xorDDT_g_nibbles
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hstep := (Finset.mem_filter.mp hx).2 i
  rw [output_nibble_equal_of_input_prefix_zero k d x i hd] at hstep
  simp only [Magma.xor, BitVec.xor_eq, BitVec.xor_self] at hstep
  exact hb' hstep.symm

/-- A fixed one-hot bit has no contribution below its containing nibble. -/
private theorem oneHot_low_prefix_zero
    (j : Fin 32) (i : Fin 8)
    (h : 4 * (i.val + 1) ≤ j.val) :
    (BitVec.ofNat 32 (2 ^ j.val)).toNat % 16 ^ (i.val + 1) = 0 := by
  have hj : 2 ^ j.val < 2 ^ 32 :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : Nat)) j.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  rw [sixteen_pow_eq_two_pow]
  exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h)

/-- The source bit has a nonzero digit in exactly its own nibble.
    This small theorem only checks the 32 possible BIT POSITIONS. -/
private theorem oneHot_own_nibble_nonzero (s : Fin 32) :
    wordDigits (BitVec.ofNat 32 (2 ^ s.val))
      (⟨s.val / 4, by omega⟩ : Fin 8) ≠ 0 := by
  fin_cases s <;> decide

/-- The structural one-hot zero pattern, with the output still in
    pre-rotation bit coordinates. -/
theorem oneHot_zero_below_input_nibble
    (k : Word) (j s : Fin 32)
    (h : s.val / 4 < j.val / 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ s.val))) = 0 := by
  let i : Fin 8 := ⟨s.val / 4, by omega⟩
  have hj : 4 * (i.val + 1) ≤ j.val := by dsimp [i]; omega
  exact xorDDT_zero_of_lower_nibble k
    (BitVec.ofNat 32 (2 ^ j.val))
    (BitVec.ofNat 32 (2 ^ s.val)) i
    (oneHot_low_prefix_zero j i hj)
    (oneHot_own_nibble_nonzero s)

/-- Undo output rotation on a one-hot bit. The corresponding original
    bit index is `(ell+21) mod 32`, since rot11 is a left rotation. -/
private theorem rot11_oneHot_unrotate (ell : Fin 32) :
    rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))) =
      BitVec.ofNat 32 (2 ^ ell.val) := by
  fin_cases ell <;> decide

/-- The full 32x32 one-hot DDT has an upper block-triangular support,
    after undoing the RFC 11-bit output rotation. ALL keys are covered. -/
theorem oneHot_matrix_lower_block_zero
    (k : Word) (j ell : Fin 32)
    (h : ((ell.val + 21) % 32) / 4 < j.val / 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 0 := by
  let s : Fin 32 := ⟨(ell.val + 21) % 32, by omega⟩
  have hs : s.val / 4 < j.val / 4 := by simpa [s] using h
  have hz := oneHot_zero_below_input_nibble k j s hs
  change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
    (rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32)))) = 0 at hz
  rw [rot11_oneHot_unrotate ell] at hz
  exact hz

/-- A compact, executable predicate indicating the 448 one-hot cells
    excluded universally for every round key. -/
def guaranteedZeroCell (j ell : Fin 32) : Prop :=
  ((ell.val + 21) % 32) / 4 < j.val / 4

instance (j ell : Fin 32) : Decidable (guaranteedZeroCell j ell) :=
  inferInstanceAs (Decidable (((ell.val + 21) % 32) / 4 < j.val / 4))

/-- Exactly 448 of the 1024 bit-position pairs are structurally
    impossible for every key. Only a 32x32 INDEX set is computed. -/
theorem guaranteedZeroCells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => guaranteedZeroCell p.1 p.2)).card = 448 := by
  decide +kernel

/-- Excluded cells are zero in the ORIGINAL Magma DDT, not merely
    in a Boolean approximation or carry-path heuristic. -/
theorem guaranteedZeroCell_sound (k : Word) (j ell : Fin 32)
    (h : guaranteedZeroCell j ell) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 0 :=
  oneHot_matrix_lower_block_zero k j ell h

end Magma.OneHotUniversalLowerNibbleZeros
