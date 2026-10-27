module

public import Magma.OneHot.ActiveNibbleNecessary
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Necessary diagonal S-box and carry masks for one-hot transitions

A real one-hot transition has equal incoming carries at its active nibble.
Except at the final nibble, its outgoing carries must also agree, since
the next unchanged nibble has zero output difference. Certified local
masks retain 76 candidate bit-position pairs and universally exclude 948,
including 52 additional diagonal exclusions. Attainability of the remaining
candidates is not asserted.

Finite checks enumerate only local digits, carry bits, and index pairs.
-/

namespace Magma.OneHotDiagonalCarryMasks

open Magma
open Magma.GProperties
open Magma.CarryAutomaton
open Magma.OneHotSilentNibbleStructure
open Magma.OneHotActiveNibbleNecessary

private abbrev Word :=
  V 32

/-- The allowed local witness for an output differing in exactly one bit.
    The final nibble is special: its carry-out is thrown away. -/
def localPossible (i : Fin 8) (r s : Fin 4) : Prop :=
  ∃ (q x : Fin 16) (c : Fin 2),
    let step := sboxCarryStep i q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    step.1 = Fin.ofNat 16 (2 ^ s.val) ∧
      (i.val = 7 ∨ step.2.1 = step.2.2)

instance (i : Fin 8) (r s : Fin 4) : Decidable (localPossible i r s) := by
  unfold localPossible
  infer_instance

/-- Four-bit masks: bit s records existence of a permissible local witness.
    The masks depend on S-box position and source-bit-within-nibble. -/
def localMask (i : Fin 8) (r : Fin 4) : Nat :=
  match i.val with
  | 0 =>
    match r.val with
    | 0 => 14
    | 1 => 7
    | 2 => 7
    | _ => 14
  | 1 =>
    match r.val with
    | 0 => 1
    | 1 => 6
    | 2 => 15
    | _ => 6
  | 2 =>
    match r.val with
    | 0 => 8
    | 1 => 14
    | 2 => 15
    | _ => 2
  | 3 =>
    match r.val with
    | 0 => 7
    | 1 => 10
    | 2 => 5
    | _ => 12
  | 4 =>
    match r.val with
    | 0 => 10
    | 1 => 14
    | 2 => 11
    | _ => 5
  | 5 =>
    match r.val with
    | 0 => 11
    | 1 => 14
    | 2 => 7
    | _ => 3
  | 6 =>
    match r.val with
    | 0 => 12
    | 1 => 12
    | 2 => 10
    | _ => 2
  | 7 =>
    match r.val with
    | 0 => 0
    | 1 => 10
    | 2 => 15
    | _ => 13
  | _ => 0

def maskAllows (i : Fin 8) (r s : Fin 4) : Prop :=
  localMask i r / 2 ^ s.val % 2 = 1

instance (i : Fin 8) (r s : Fin 4) : Decidable (maskAllows i r s) := by
  unfold maskAllows
  infer_instance

/-- All 128 local assertions can be kernel-verified independently of k.
    There is no `decide` on 32-bit input or output words. -/
theorem maskAllows_iff_localPossible (i : Fin 8) (r s : Fin 4) :
    maskAllows i r s ↔ localPossible i r s := by
  revert i r s
  decide +kernel

/-! ## The necessary local witness extracted from a real DDT transition. -/

private theorem xorDigit_zero_right (v : Fin 16) : xorDigit v 0 = v := by fin_cases v <;> decide

/-- Two digit streams with the same prefix yield equal incoming carries. -/
private theorem incomingCarry_congr_prefix
    (xs ys ks : Nat → Fin 16) (n : Nat)
    (h : ∀ j, j < n → xs j = ys j) :
    incomingCarry xs ks n = incomingCarry ys ks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (by
        intro j hj
        exact h j (by omega))
      change nextCarry (xs n) (ks n) (incomingCarry xs ks n) =
        nextCarry (ys n) (ks n) (incomingCarry ys ks n)
      rw [h n (by omega), hp]

private theorem pairCarry_diagonal_of_lower_zero (k d x : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) :
    (wordCarryPair k d x i.val).1 = (wordCarryPair k d x i.val).2 := by
  change
    incomingCarry (wordDigitStream x) (wordDigitStream k) i.val =
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
    _ = wordDigitStream (xor x d) n := (wordDigitStream_at (xor x d) u).symm

private theorem oneHot_other_nibble_zero (j : Fin 32) (i : Fin 8) (h : i.val ≠ j.val / 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) i = 0 := by
  revert h
  fin_cases j <;> fin_cases i <;> decide

private theorem oneHot_own_nibble (j : Fin 32) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) (⟨j.val / 4, by omega⟩ : Fin 8) =
      Fin.ofNat 16 (2 ^ (j.val % 4)) := by
  fin_cases j <;> decide

private theorem oneHot_neighbor_zero (j : Fin 32) (i : Fin 8) (hi : i.val = j.val / 4)
    (hn : i.val < 7) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) (⟨i.val + 1, by omega⟩ : Fin 8) = 0 := by
  exact
    oneHot_other_nibble_zero j _
      (by
        dsimp; omega)

/-- If a REAL transition has only an active output bit in the first
    changed input nibble, it yields a local S-box witness with equal
    incoming carries and (except at nibble seven) equal outgoing carries. -/
private theorem real_transition_implies_local
    (k x : Word) (j s : Fin 32)
    (hsame : j.val / 4 = s.val / 4)
    (haccept : ∀ t : Fin 8,
      xor (π t (Internal.nibble (modShift k
        (xor x (BitVec.ofNat 32 (2 ^ j.val)))) t))
        (π t (Internal.nibble (modShift k x) t)) =
          Internal.nibble (BitVec.ofNat 32 (2 ^ s.val)) t) :
    localPossible (⟨j.val / 4, by omega⟩ : Fin 8)
      (⟨j.val % 4, by omega⟩ : Fin 4)
      (⟨s.val % 4, by omega⟩ : Fin 4) := by
  let d : Word := BitVec.ofNat 32 (2 ^ j.val)
  let b : Word := BitVec.ofNat 32 (2 ^ s.val)
  let i : Fin 8 := ⟨j.val / 4, by omega⟩
  let r : Fin 4 := ⟨j.val % 4, by omega⟩
  let z : Fin 4 := ⟨s.val % 4, by omega⟩
  have hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0 := by
    intro u hu
    exact oneHot_other_nibble_zero j u (by dsimp [i] at hu; omega)
  have hc := pairCarry_diagonal_of_lower_zero k d x i hlow
  let c : Fin 2 := (wordCarryPair k d x i.val).1
  have hstate : wordCarryPair k d x i.val = (c, c) := by
    apply Prod.ext <;> simp [c, hc]
  have hdigit : wordDigits d i = Fin.ofNat 16 (2 ^ r.val) := by
    simpa only [d, i, r] using oneHot_own_nibble j
  have htarget : wordDigits b i = Fin.ofNat 16 (2 ^ z.val) := by
    have hii : i = (⟨s.val / 4, by omega⟩ : Fin 8) :=
      Fin.ext (by dsimp [i]; omega)
    rw [hii]
    simpa only [b, z] using oneHot_own_nibble s
  have hgood (u : Fin 8) :
      localSBoxDifference k d x u = wordDigits b u :=
    (localSBoxDifference_eq_iff k d b x u).mpr (haccept u)
  let st := sboxCarryStep i (wordDigits k i)
      (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c, c)
  have hstep : st =
      (localSBoxDifference k d x i, wordCarryPair k d x (i.val + 1)) := by
    simpa only [st, hdigit, hstate] using
      (sboxCarryStep_word_correct k d x i)
  have ho : st.1 = Fin.ofNat 16 (2 ^ z.val) := by
    rw [hstep, hgood i, htarget]
  have hcarry : i.val = 7 ∨ st.2.1 = st.2.2 := by
    by_cases hlast : i.val = 7
    · exact Or.inl hlast
    · have hnext : i.val < 7 := by omega
      let next : Fin 8 := ⟨i.val + 1, by omega⟩
      have hdnext : wordDigits d next = 0 :=
        oneHot_neighbor_zero j i (by rfl) hnext
      have hbnext : wordDigits b next = 0 := by
        exact oneHot_other_nibble_zero s next
          (by dsimp [next, i]; omega)
      have hnextstep := congrArg Prod.fst
        (sboxCarryStep_word_correct k d x next)
      have hzero :
          (sboxCarryStep next (wordDigits k next) 0
            (wordDigits x next) (wordCarryPair k d x next.val)).1 = 0 := by
        rw [hdnext] at hnextstep
        rw [hgood next, hbnext] at hnextstep
        exact hnextstep
      have hcnext :
          (wordCarryPair k d x next.val).1 =
            (wordCarryPair k d x next.val).2 :=
        silent_sbox_zero_forces_diagonal next (wordDigits k next)
          (wordDigits x next) _ _ hzero
      right
      rw [hstep]
      exact hcnext
  exact ⟨wordDigits k i, wordDigits x i, c, ho, hcarry⟩

/-- Real positive DDT support implies the 4-bit mask permits the cell. -/
theorem diagonal_positive_implies_mask
    (k : Word) (j s : Fin 32)
    (hsame : j.val / 4 = s.val / 4)
    (hp : 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ s.val)))) :
    maskAllows (⟨j.val / 4, by omega⟩ : Fin 8)
      (⟨j.val % 4, by omega⟩ : Fin 4)
      (⟨s.val % 4, by omega⟩ : Fin 4) := by
  rw [xorDDT_g_eq_nibbles] at hp
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
  have haccept := (Finset.mem_filter.mp hx).2
  have hpossible := real_transition_implies_local k x j s hsame haccept
  exact (maskAllows_iff_localPossible _ _ _).mpr hpossible

/-! ## The 76-cell candidate grid in original (post-rotation) indices. -/

/-- Reindex the rotated output bit back to the active source nibble. -/
private theorem rot11_oneHot_unrotate (ell : Fin 32) :
    rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))) =
      BitVec.ofNat 32 (2 ^ ell.val) := by
  fin_cases ell <;> decide

/-- This predicate is a PROVEN NECESSARY condition, not an assertion
    that every permitted cell is attainable for some key. -/
def candidateCell (j ell : Fin 32) : Prop :=
  let s : Nat := (ell.val + 21) % 32
  j.val / 4 = s / 4 ∧
    maskAllows (⟨j.val / 4, by omega⟩ : Fin 8)
      (⟨j.val % 4, by omega⟩ : Fin 4)
      (⟨s % 4, by omega⟩ : Fin 4)

instance (j ell : Fin 32) : Decidable (candidateCell j ell) := by
  unfold candidateCell
  infer_instance

/-- The exact NUMBER of cells surviving BOTH structural constraints.
    This is a 1024-element INDEX computation, not a full-word DDT. -/
theorem candidateCells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => candidateCell p.1 p.2)).card = 76 := by
  decide +kernel

/-- Conversely 948 cells are universally excluded, for EVERY key. -/
theorem excludedCells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => ¬ candidateCell p.1 p.2)).card = 948 := by
  decide +kernel

/-- Exactly 52 of the 128 diagonal nibble cells fail the certified
    local S-box/carry test. These are additional universal zeros. -/
theorem additionallyExcludedDiagonal_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 =>
        ((p.2.val + 21) % 32) / 4 = p.1.val / 4 ∧
          ¬ candidateCell p.1 p.2)).card = 52 := by
  decide +kernel

/-- New universal-zero theorem, combining the earlier 896 exclusions
    with 52 additional local S-box/carry exclusions on the diagonal. -/
theorem oneHot_DDT_zero_of_not_candidate (k : Word) (j ell : Fin 32)
    (h : ¬ candidateCell j ell) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  let s : Fin 32 := ⟨(ell.val + 21) % 32, by omega⟩
  have hs : 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ s.val))) := by
    change 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))))
    rw [rot11_oneHot_unrotate ell]
    exact hp
  have hsamenibble : j.val / 4 = s.val / 4 := by
    symm
    exact oneHot_positive_implies_same_nibble k j ell hp
  have hmask := diagonal_positive_implies_mask k j s hsamenibble hs
  apply h
  exact ⟨hsamenibble, hmask⟩

/-- Thus at most 76 of 1024 one-hot-to-one-hot DDT entries are
    positive, for every round key. No probabilities are assumed. -/
theorem positiveOneHotCells_card_le_76 (k : Word) :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g k
        (BitVec.ofNat 32 (2 ^ p.1.val))
        (BitVec.ofNat 32 (2 ^ p.2.val)))).card ≤ 76 := by
  have hs :
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => 0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)))) ⊆
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => candidateCell p.1 p.2)) := by
    intro p hp
    rcases p with ⟨j, ell⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    by_contra hn
    exact (Nat.ne_of_gt hp) (oneHot_DDT_zero_of_not_candidate k j ell hn)
  calc
    _ ≤ ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
          (fun p : Fin 32 × Fin 32 => candidateCell p.1 p.2)).card := Finset.card_le_card hs
    _ = 76 := candidateCells_card

end Magma.OneHotDiagonalCarryMasks
