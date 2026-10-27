module

public import Magma.OneHot.SilentNibbleStructure
import all Init.Data.Range.Basic

@[expose] public section

/-!
# The first active input nibble must remain active

For an arbitrary nonzero input difference, the two modular additions have
identical carries into the first changed nibble. Its nonzero difference
survives the bijective S-box for every round key.

For one-hot input and output differences this restricts positive DDT
entries to eight diagonal nibble blocks after undoing the output rotation.
The 896 off-diagonal index pairs are universally zero, leaving at most
128 positive entries. Closed computations enumerate only bit positions
and nibble indices.
-/

namespace Magma.OneHotActiveNibbleNecessary

open Magma
open Magma.CarryAutomaton
open Magma.OneHotSilentNibbleStructure

private abbrev Word :=
  V 32

/-- XOR of a 4-bit digit with the zero digit. -/
private theorem xorDigit_zero_right (v : Fin 16) : xorDigit v 0 = v := by
  fin_cases v <;> decide

/-- Two input-digit streams that agree strictly below index n
    produce identical carries into index n under the same key. -/
private theorem incomingCarry_congr_prefix
    (xs ys ks : Nat → Fin 16) (n : Nat)
    (h : ∀ j : Nat, j < n → xs j = ys j) :
    incomingCarry xs ks n = incomingCarry ys ks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp : incomingCarry xs ks n = incomingCarry ys ks n :=
        ih (by
          intro j hj
          exact h j (by omega))
      change nextCarry (xs n) (ks n) (incomingCarry xs ks n) =
        nextCarry (ys n) (ks n) (incomingCarry ys ks n)
      rw [h n (by omega), hp]

/-- The two additions entering the first nonzero-difference nibble
    have the SAME incoming carry bit. This is a structural property
    of modular addition, not an independence assumption. -/
private theorem wordCarryPair_diagonal_of_lower_zero
    (k d x : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) :
    (wordCarryPair k d x i.val).1 =
      (wordCarryPair k d x i.val).2 := by
  change incomingCarry (wordDigitStream x) (wordDigitStream k) i.val =
    incomingCarry (wordDigitStream (xor x d)) (wordDigitStream k) i.val
  apply incomingCarry_congr_prefix
  intro n hn
  have hn8 : n < 8 := by omega
  let u : Fin 8 := ⟨n, hn8⟩
  have hd : wordDigits d u = 0 := hlow u (by simpa [u] using hn)
  have hxor : wordDigits (xor x d) u = wordDigits x u := by
    rw [wordDigits_xor, hd, xorDigit_zero_right]
  calc
    wordDigitStream x n = wordDigits x u := wordDigitStream_at x u
    _ = wordDigits (xor x d) u := hxor.symm
    _ = wordDigitStream (xor x d) n :=
      (wordDigitStream_at (xor x d) u).symm

/-- A nonzero input difference in its first active nibble cannot
    disappear after modular addition and the bijective RFC S-box. -/
theorem firstActiveNibble_nonzero
    (k d x : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0)
    (hactive : wordDigits d i ≠ 0) :
    localSBoxDifference k d x i ≠ 0 := by
  have hc := wordCarryPair_diagonal_of_lower_zero k d x i hlow
  have hs : wordCarryPair k d x i.val =
      ((wordCarryPair k d x i.val).1,
       (wordCarryPair k d x i.val).1) := by
    apply Prod.ext <;> simp [hc]
  have ha := active_sbox_step_nonzero i
    (wordDigits k i) (wordDigits d i) (wordDigits x i)
    (wordCarryPair k d x i.val).1 hactive
  have hcorrect := congrArg Prod.fst (sboxCarryStep_word_correct k d x i)
  rw [hs] at hcorrect
  intro hz
  apply ha
  exact hcorrect.trans hz

/-- UNIVERSAL active-nibble exclusion for arbitrary input difference d.
    If i is the FIRST changed input nibble, then output nibble i
    cannot be zero. All 32-bit round keys and all output words are covered. -/
theorem xorDDT_zero_if_first_active_nibble_is_silent
    (k d b : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0)
    (hactive : wordDigits d i ≠ 0)
    (hb : wordDigits b i = 0) :
    xorDDT_g k d (rot11 b) = 0 := by
  rw [xorDDT_g_eq_nibbles]
  unfold xorDDT_g_nibbles
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlocal := firstActiveNibble_nonzero k d x i hlow hactive
  have hcheck := (Finset.mem_filter.mp hx).2 i
  have heq := (localSBoxDifference_eq_iff k d b x i).mpr hcheck
  exact hlocal (heq.trans hb)

/-! ## Specialization to one-hot input/output differences. -/

/-- A one-hot input digit vanishes everywhere except its active nibble.
    Only 32×8 closed INDEX cases, not 32-bit inputs, are evaluated. -/
private theorem oneHot_other_nibble_zero
    (j : Fin 32) (i : Fin 8)
    (h : i.val ≠ j.val / 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) i = 0 := by
  revert h
  fin_cases j <;> fin_cases i <;> decide

/-- The active input nibble of a one-hot word is genuinely nonzero. -/
private theorem oneHot_own_nibble_nonzero (j : Fin 32) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val))
      (⟨j.val / 4, by omega⟩ : Fin 8) ≠ 0 := by
  fin_cases j <;> decide

/-- Any one-hot OUTPUT in a different nibble is IMPOSSIBLE, even
    if that output nibble is HIGHER than the input nibble.
    Here s is the output bit index BEFORE the final rotation. -/
theorem oneHot_off_diagonal_unrotated_zero
    (k : Word) (j s : Fin 32)
    (h : s.val / 4 ≠ j.val / 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ s.val))) = 0 := by
  let i : Fin 8 := ⟨j.val / 4, by omega⟩
  have hlow : ∀ u : Fin 8, u.val < i.val →
      wordDigits (BitVec.ofNat 32 (2 ^ j.val)) u = 0 := by
    intro u hu
    exact oneHot_other_nibble_zero j u (by dsimp [i] at hu; omega)
  have ha : wordDigits (BitVec.ofNat 32 (2 ^ j.val)) i ≠ 0 :=
    oneHot_own_nibble_nonzero j
  have hb : wordDigits (BitVec.ofNat 32 (2 ^ s.val)) i = 0 :=
    oneHot_other_nibble_zero s i (by dsimp [i]; omega)
  exact xorDDT_zero_if_first_active_nibble_is_silent
    k (BitVec.ofNat 32 (2 ^ j.val))
    (BitVec.ofNat 32 (2 ^ s.val)) i hlow ha hb

/-- Convert the bit of the original g output into its pre-rotation
    index: rotation by 11 is inverted by adding 21 modulo 32. -/
private theorem rot11_oneHot_unrotate (ell : Fin 32) :
    rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))) =
      BitVec.ofNat 32 (2 ^ ell.val) := by
  fin_cases ell <;> decide

/-- The full one-hot 32×32 XOR-DDT is BLOCK-DIAGONAL in nibble indices,
    after compensating the final 11-bit output rotation. No assumption
    about key bits, carries, or S-box differential probabilities. -/
theorem oneHot_matrix_off_diagonal_zero
    (k : Word) (j ell : Fin 32)
    (h : ((ell.val + 21) % 32) / 4 ≠ j.val / 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 0 := by
  let s : Fin 32 := ⟨(ell.val + 21) % 32, by omega⟩
  have hs : s.val / 4 ≠ j.val / 4 := by simpa [s] using h
  have hz := oneHot_off_diagonal_unrotated_zero k j s hs
  change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32)))) = 0 at hz
  rw [rot11_oneHot_unrotate ell] at hz
  exact hz

/-- One-hot input/output bit positions with different active nibble
    after undoing the RFC 11-bit rotation. -/
def guaranteedOffDiagonal (j ell : Fin 32) : Prop :=
  ((ell.val + 21) % 32) / 4 ≠ j.val / 4

instance (j ell : Fin 32) : Decidable (guaranteedOffDiagonal j ell) :=
  inferInstanceAs (Decidable (((ell.val + 21) % 32) / 4 ≠ j.val / 4))

/-- The 896 off-diagonal bit-position pairs are universally zero.
    Only 8 diagonal blocks of size 4×4 (128 positions) remain. -/
theorem guaranteedOffDiagonal_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => guaranteedOffDiagonal p.1 p.2)).card = 896 := by
  decide +kernel

/-- End-to-end soundness of the 896-cell structural exclusion. -/
theorem guaranteedOffDiagonal_sound (k : Word) (j ell : Fin 32)
    (h : guaranteedOffDiagonal j ell) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 0 :=
  oneHot_matrix_off_diagonal_zero k j ell h

/-- Conversely, a positive one-hot transition MUST remain in the
    same nibble after undoing rotation. -/
theorem oneHot_positive_implies_same_nibble
    (k : Word) (j ell : Fin 32)
    (hpos : 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val))) :
    ((ell.val + 21) % 32) / 4 = j.val / 4 := by
  by_contra hneq
  have hz := oneHot_matrix_off_diagonal_zero k j ell hneq
  omega

/-- The 128 potentially nonzero positions, a union of eight 4×4
    diagonal nibble blocks. Counting only bit-position pairs. -/
theorem diagonalCells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => ((p.2.val + 21) % 32) / 4 = p.1.val / 4)).card = 128 := by
  decide +kernel

/-- For ANY key, there are at most 128 positive entries among the
    1024 one-hot-to-one-hot DDT entries. This is a structural upper
    bound on SUPPORT SIZE, not a bound on differential probability. -/
theorem positiveOneHotCells_card_le_128 (k : Word) :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g k
        (BitVec.ofNat 32 (2 ^ p.1.val))
        (BitVec.ofNat 32 (2 ^ p.2.val)))).card ≤ 128 := by
  have hs :
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)))) ⊆
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => ((p.2.val + 21) % 32) / 4 = p.1.val / 4)) := by
    intro p hp
    rcases p with ⟨j, ell⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact oneHot_positive_implies_same_nibble k j ell hp
  calc
    _ ≤ ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
          (fun p : Fin 32 × Fin 32 => ((p.2.val + 21) % 32) / 4 = p.1.val / 4)).card :=
      Finset.card_le_card hs
    _ = 128 := diagonalCells_card

end Magma.OneHotActiveNibbleNecessary
