module

public import Magma.DDT.OneHot.Mechanics.ExactCarryRegimes
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Completeness of exact local one-hot support

A locally permitted digit and reachable incoming carry extend to a real
full-word input: replacing the active digit preserves the prefix carry,
and matching outgoing carries keep every later output nibble silent.
The reverse implication retains the actual carry of a real transition.

Thus the eight exact local tables characterize the original fixed-key
one-hot DDT support, and their counts sum to its exact cardinality for
every round key. The proof constructs witnesses and reindexes finite
sets without enumerating the 32-bit input or key space.
-/

namespace Magma.OneHotExactLocalSupportCompleteness

open Magma
open Magma.GProperties
open Magma.OneHotActiveNibbleNecessary
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotFixedKeySupport72
open Magma.OneHotExactCarryRegimes
open Magma.OneHotSilentNibbleStructure

private abbrev Word :=
  V 32

private abbrev Cell :=
  Fin 32 × Fin 32

private abbrev Local :=
  Fin 4 × Fin 4

private abbrev Triple :=
  Fin 8 × Local

private def srcBit (i : Fin 8) (r : Fin 4) : Fin 32 :=
  ⟨4 * i.val + r.val, by omega⟩

private def dstBit (i : Fin 8) (s : Fin 4) : Fin 32 :=
  ⟨(4 * i.val + s.val + 11) % 32, by omega⟩

private theorem oneHot_active_digit (i : Fin 8) (r : Fin 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val))) i = Fin.ofNat 16 (2 ^ r.val) := by
  fin_cases i <;> fin_cases r <;> decide

private theorem rotate_oneHot_digit (i : Fin 8) (s : Fin 4) :
    rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) = BitVec.ofNat 32 (2 ^ (dstBit i s).val) := by
  fin_cases i <;> fin_cases s <;> decide

private theorem xorDigit_zero_right (v : Fin 16) : xorDigit v 0 = v := by fin_cases v <;> decide

private theorem xorDigit_self (v : Fin 16) : xorDigit v v = 0 := by fin_cases v <;> decide

/-- Any nibble with zero input difference and equal incoming carries
    has zero output difference, independently of key and input. -/
private theorem silent_step_zero (i : Fin 8) (q a : Fin 16) (c : Fin 2) :
    (sboxCarryStep i q 0 a (c,c)).1 = 0 := by
  unfold sboxCarryStep
  rw [xorDigit_zero_right]
  exact xorDigit_self _

private theorem incomingCarry_congr_prefix (xs ys ks : Nat → Fin 16) (n : Nat)
    (h : ∀ j, j < n → xs j = ys j) : incomingCarry xs ks n = incomingCarry ys ks n := by
  induction n with
  | zero => rfl
  | succ n
    ih =>
    have hp :=
      ih
        (by
          intro j hj
          exact h j (by omega))
    change
      nextCarry (xs n) (ks n) (incomingCarry xs ks n) =
        nextCarry (ys n) (ks n) (incomingCarry ys ks n)
    rw [h n (by omega), hp]

private theorem oneHot_other_nibble_zero (j : Fin 32) (i : Fin 8) (h : i.val ≠ j.val / 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) i = 0 := by
  revert h
  fin_cases j <;> fin_cases i <;> decide

private theorem oneHot_own_nibble (j : Fin 32) :
    wordDigits (BitVec.ofNat 32 (2 ^ j.val)) (⟨j.val / 4, by omega⟩ : Fin 8) =
      Fin.ofNat 16 (2 ^ (j.val % 4)) := by
  fin_cases j <;> decide

private theorem carryPair_diagonal_of_lower_zero (k d x : Word) (i : Fin 8)
    (hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0) :
    (wordCarryPair k d x i.val).1 = (wordCarryPair k d x i.val).2 := by
  change
    incomingCarry (wordDigitStream x) (wordDigitStream k) i.val =
      incomingCarry (wordDigitStream (xor x d)) (wordDigitStream k) i.val
  apply incomingCarry_congr_prefix
  intro n hn
  let u : Fin 8 := ⟨n, by omega⟩
  have hd : wordDigits d u = 0 := hlow u (by simpa [u] using hn)
  have hxor : wordDigits (xor x d) u = wordDigits x u := by
    rw [wordDigits_xor, hd, xorDigit_zero_right]
  calc
    wordDigitStream x n = wordDigits x u := wordDigitStream_at x u
    _ = wordDigits (xor x d) u := hxor.symm
    _ = wordDigitStream (xor x d) n := (wordDigitStream_at (xor x d) u).symm

/-! ## 1. A local possibility is precisely a digit-and-carry witness. -/

theorem exact_localPotential_iff_witness (k : Word) (i : Fin 8) (r s : Fin 4) :
    localPotential i (wordDigits k i) (exactCarryFlag k i) r s = true ↔
      ∃ (a : Fin 16) (c : Fin 2),
        (c = 0 ∨ (exactCarryFlag k i = true ∧ c = 1)) ∧
          (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).1 =
            Fin.ofNat 16 (2 ^ s.val) ∧
          (i.val = 7 ∨
            (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.1 =
              (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.2) := by
  constructor
  · intro h
    unfold localPotential at h
    obtain ⟨a, _, ha⟩ := List.any_eq_true.mp h
    obtain ⟨c, _, hc⟩ := List.any_eq_true.mp ha
    by_cases hallowed : c = 0 ∨ (exactCarryFlag k i = true ∧ c = 1)
    · simp only [ite_eq_left hallowed, decide_eq_true_eq] at hc
      exact ⟨a, c, hallowed, hc.1, hc.2⟩
    · simp [hallowed] at hc
  · rintro ⟨a, c, hc, ho, hout⟩
    unfold localPotential
    apply List.any_eq_true.mpr
    refine ⟨a, by simp, ?_⟩
    apply List.any_eq_true.mpr
    refine ⟨c, by simp, ?_⟩
    simp only [ite_eq_left hc, decide_eq_true_eq]
    exact ⟨ho, hout⟩

/-! ## 2. Substitute a local nibble without changing its prefix carry. -/

/-- Construct a full input preserving the lower prefix of `x₀` while
    replacing its digit at i by the arbitrarily prescribed `a`. -/
private def replaceDigit (x₀ : Word) (i : Fin 8) (a : Fin 16) : Word :=
  wordDigitsEquiv.symm (fun u => if u = i then a else wordDigits x₀ u)

private theorem replaceDigit_at (x₀ : Word) (i : Fin 8) (a : Fin 16) (u : Fin 8) :
    wordDigits (replaceDigit x₀ i a) u = if u = i then a else wordDigits x₀ u := by
  exact congrFun (wordDigitsEquiv.apply_symm_apply _) u

private theorem replaceDigit_active (x₀ : Word) (i : Fin 8) (a : Fin 16) :
    wordDigits (replaceDigit x₀ i a) i = a := by
  rw [replaceDigit_at]
  simp

private theorem replaceDigit_incomingCarry (k x₀ : Word) (i : Fin 8) (a : Fin 16) :
    incomingCarry (wordDigitStream (replaceDigit x₀ i a)) (wordDigitStream k) i.val =
      incomingCarry (wordDigitStream x₀) (wordDigitStream k) i.val := by
  apply incomingCarry_congr_prefix
  intro n hn
  let u : Fin 8 := ⟨n, by omega⟩
  have hu : u ≠ i := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [u] at hv
    omega
  calc
    wordDigitStream (replaceDigit x₀ i a) n = wordDigits (replaceDigit x₀ i a) u :=
      wordDigitStream_at _ u
    _ = wordDigits x₀ u := by
      rw [replaceDigit_at]; simp [hu]
    _ = wordDigitStream x₀ n := (wordDigitStream_at _ u).symm

/-! ## 3. A local witness extends to a real full-word differential. -/

private theorem exact_local_witness_realized (k : Word) (i : Fin 8) (r s : Fin 4) (a : Fin 16)
    (c : Fin 2) (hc : c = 0 ∨ (exactCarryFlag k i = true ∧ c = 1))
    (ho :
      (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).1 =
        Fin.ofNat 16 (2 ^ s.val))
    (hout :
      i.val = 7 ∨
        (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.1 =
          (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.2) :
    0 <
      xorDDT_g k (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
        (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) := by
  obtain ⟨x₀, hc₀⟩ := (incomingCarry_reachable_iff k i c).mpr (hc.imp id (fun h => ⟨h.2, h.1⟩))
  let x := replaceDigit x₀ i a
  let j : Fin 32 := ⟨4 * i.val + r.val, by omega⟩
  let z : Fin 32 := ⟨4 * i.val + s.val, by omega⟩
  let d : Word := BitVec.ofNat 32 (2 ^ j.val)
  let b : Word := BitVec.ofNat 32 (2 ^ z.val)
  have hdi : wordDigits d i = Fin.ofNat 16 (2 ^ r.val) := by exact oneHot_active_digit i r
  have hbi : wordDigits b i = Fin.ofNat 16 (2 ^ s.val) := by exact oneHot_active_digit i s
  have hdother (u : Fin 8) (hu : u ≠ i) : wordDigits d u = 0 := by
    apply oneHot_other_nibble_zero j u
    intro he
    apply hu
    apply Fin.ext
    dsimp [j] at he
    omega
  have hbother (u : Fin 8) (hu : u ≠ i) : wordDigits b u = 0 := by
    apply oneHot_other_nibble_zero z u
    intro he
    apply hu
    apply Fin.ext
    dsimp [z] at he
    omega
  have hci : (wordCarryPair k d x i.val).1 = c := by
    change incomingCarry (wordDigitStream x) (wordDigitStream k) i.val = c
    rw [replaceDigit_incomingCarry]
    exact hc₀
  have hdiag : (wordCarryPair k d x i.val).1 = (wordCarryPair k d x i.val).2 := by
    apply carryPair_diagonal_of_lower_zero
    intro u hu
    apply hdother u
    intro hui
    have hv := congrArg Fin.val hui
    omega
  have hstate : wordCarryPair k d x i.val = (c, c) := Prod.ext hci (hdiag.symm.trans hci)
  let step := sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) a (c, c)
  have hxi : wordDigits x i = a := replaceDigit_active x₀ i a
  have hstep : step = (localSBoxDifference k d x i, wordCarryPair k d x (i.val + 1)) := by
    simpa only [hdi, hxi, hstate] using (sboxCarryStep_word_correct k d x i)
  have hactive : localSBoxDifference k d x i = wordDigits b i := by
    have hfst := congrArg Prod.fst hstep
    exact (hfst.symm.trans ho).trans hbi.symm
  have hafter :
    i.val < 7 → (wordCarryPair k d x (i.val + 1)).1 = (wordCarryPair k d x (i.val + 1)).2 := by
    intro hi
    rcases hout with hlast | hsame
    · omega
    · have hh := congrArg Prod.snd hstep
      dsimp only at hh
      rw [hh] at hsame
      exact hsame
  have hprop :
    ∀ n : Nat, i.val < n → n ≤ 7 → (wordCarryPair k d x n).1 = (wordCarryPair k d x n).2 := by
    intro n
    induction n with
    | zero =>
      intro h _; omega
    | succ n ih =>
      intro hi hn
      by_cases hbase : n = i.val
      · subst n
        exact hafter (by omega)
      · have hprev : (wordCarryPair k d x n).1 = (wordCarryPair k d x n).2 :=
          ih (by omega) (by omega)
        let u : Fin 8 := ⟨n, by omega⟩
        have hdu : wordDigits d u = 0 :=
          hdother u
            (by
              intro h
              have he := congrArg Fin.val h
              dsimp [u] at he
              omega)
        have hxu : wordDigitStream (xor x d) n = wordDigitStream x n := by
          rw [wordDigitStream_at (xor x d) u, wordDigitStream_at x u, wordDigits_xor, hdu,
            xorDigit_zero_right]
        change
          nextCarry (wordDigitStream x n) (wordDigitStream k n) (wordCarryPair k d x n).1 =
            nextCarry (wordDigitStream (xor x d) n) (wordDigitStream k n) (wordCarryPair k d x n).2
        rw [hxu, hprev]
  have houtput : ∀ u : Fin 8, localSBoxDifference k d x u = wordDigits b u := by
    intro u
    by_cases hui : u = i
    · subst u
      exact hactive
    · have hdu : wordDigits d u = 0 := hdother u hui
      have hbu : wordDigits b u = 0 := hbother u hui
      have hcdiag : (wordCarryPair k d x u.val).1 = (wordCarryPair k d x u.val).2 := by
        by_cases hbefore : u.val < i.val
        · apply carryPair_diagonal_of_lower_zero
          intro v hv
          apply hdother v
          intro hvi
          have he := congrArg Fin.val hvi
          omega
        · exact hprop u.val (by omega) (by omega)
      have hstateu :
        wordCarryPair k d x u.val =
          ((wordCarryPair k d x u.val).1, (wordCarryPair k d x u.val).1) :=
        Prod.ext rfl hcdiag.symm
      have hstepu := congrArg Prod.fst (sboxCarryStep_word_correct k d x u)
      dsimp only at hstepu
      rw [hdu, hstateu] at hstepu
      rw [hbu, ← hstepu]
      exact silent_step_zero u (wordDigits k u) (wordDigits x u) (wordCarryPair k d x u.val).1
  have haccept :
    ∀ u : Fin 8,
      xor (π u (Internal.nibble (modShift k (xor x d)) u))
          (π u (Internal.nibble (modShift k x) u)) =
        Internal.nibble b u := by
    intro u
    exact (localSBoxDifference_eq_iff k d b x u).mp (houtput u)
  change 0 < xorDDT_g k d (rot11 b)
  rw [xorDDT_g_eq_nibbles]
  unfold xorDDT_g_nibbles
  apply Finset.card_pos.mpr
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haccept⟩⟩

/-! The reverse direction must use the ACTUAL carry from a real
    input, not the conservative `feasibleCarryFlag` of the earlier bridge. -/

private theorem real_oneHot_implies_exact_local (k : Word) (i : Fin 8) (r s : Fin 4)
    (hp :
      0 <
        xorDDT_g k (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
          (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))))) :
    localPotential i (wordDigits k i) (exactCarryFlag k i) r s = true := by
  let j : Fin 32 := ⟨4 * i.val + r.val, by omega⟩
  let z : Fin 32 := ⟨4 * i.val + s.val, by omega⟩
  let d : Word := BitVec.ofNat 32 (2 ^ j.val)
  let b : Word := BitVec.ofNat 32 (2 ^ z.val)
  change 0 < xorDDT_g k d (rot11 b) at hp
  rw [xorDDT_g_eq_nibbles] at hp
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
  have haccept := (Finset.mem_filter.mp hx).2
  have hgood (u : Fin 8) : localSBoxDifference k d x u = wordDigits b u :=
    (localSBoxDifference_eq_iff k d b x u).mpr (haccept u)
  have hlow : ∀ u : Fin 8, u.val < i.val → wordDigits d u = 0 := by
    intro u hu
    apply oneHot_other_nibble_zero j u
    dsimp [j]
    omega
  have hdiag := carryPair_diagonal_of_lower_zero k d x i hlow
  let c : Fin 2 := (wordCarryPair k d x i.val).1
  have hallowed : c = 0 ∨ (exactCarryFlag k i = true ∧ c = 1) := by
    exact ((incomingCarry_reachable_iff k i c).mp ⟨x, rfl⟩).imp id (fun h => ⟨h.2, h.1⟩)
  have hstate : wordCarryPair k d x i.val = (c, c) := Prod.ext rfl (hdiag.symm)
  have hdi : wordDigits d i = Fin.ofNat 16 (2 ^ r.val) := by exact oneHot_active_digit i r
  have hbi : wordDigits b i = Fin.ofNat 16 (2 ^ s.val) := by exact oneHot_active_digit i s
  have hstep := sboxCarryStep_word_correct k d x i
  rw [hdi, hstate] at hstep
  have hout :
    (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c, c)).1 =
      Fin.ofNat 16 (2 ^ s.val) := by
    have hh := congrArg Prod.fst hstep
    simpa only [hgood i, hbi] using hh
  have hcarry :
    i.val = 7 ∨
      (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i) (c, c)).2.1 =
        (sboxCarryStep i (wordDigits k i) (Fin.ofNat 16 (2 ^ r.val)) (wordDigits x i)
            (c, c)).2.2 := by
    by_cases hlast : i.val = 7
    · exact Or.inl hlast
    · have hnext : i.val < 7 := by omega
      let next : Fin 8 := ⟨i.val + 1, by omega⟩
      have hdn : wordDigits d next = 0 := by
        apply oneHot_other_nibble_zero j next
        dsimp [next, j]
        omega
      have hbn : wordDigits b next = 0 := by
        apply oneHot_other_nibble_zero z next
        dsimp [next, z]
        omega
      have hstepnext := congrArg Prod.fst (sboxCarryStep_word_correct k d x next)
      rw [hdn, hgood next, hbn] at hstepnext
      have hcnext : (wordCarryPair k d x next.val).1 = (wordCarryPair k d x next.val).2 :=
        silent_sbox_zero_forces_diagonal next (wordDigits k next) (wordDigits x next) _ _ hstepnext
      right
      have hh := congrArg Prod.snd hstep
      dsimp only at hh
      rw [hh]
      exact hcnext
  apply (exact_localPotential_iff_witness k i r s).mpr
  exact ⟨wordDigits x i, c, hallowed, hout, hcarry⟩

/-- Exact 16-cell local feasibility coincides with genuine DDT support
    for the corresponding diagonal block. -/
theorem localPotential_exact_iff_real
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    localPotential i (wordDigits k i) (exactCarryFlag k i) r s = true ↔
      0 < fastOneHotDDT k (srcBit i r) (dstBit i s) := by
  constructor
  · intro hl
    obtain ⟨a,c,hc,ho,hout⟩ :=
      (exact_localPotential_iff_witness k i r s).mp hl
    have hp := exact_local_witness_realized k i r s a c hc ho hout
    have hrot : rot11 (BitVec.ofNat 32 (2^(4*i.val+s.val))) =
        BitVec.ofNat 32 (2^(dstBit i s).val) := by
      exact rotate_oneHot_digit i s
    rw [hrot] at hp
    rw [fastOneHotDDT_correct]
    simpa only [srcBit] using hp
  · intro hp
    have hpos : 0 < xorDDT_g k
        (BitVec.ofNat 32 (2^(srcBit i r).val))
        (BitVec.ofNat 32 (2^(dstBit i s).val)) := by
      rw [← fastOneHotDDT_correct]
      exact hp
    have hrot : rot11 (BitVec.ofNat 32 (2^(4*i.val+s.val))) =
        BitVec.ofNat 32 (2^(dstBit i s).val) := by
      exact rotate_oneHot_digit i s
    have hpos' : 0 < xorDDT_g k
        (BitVec.ofNat 32 (2^(4*i.val+r.val)))
        (rot11 (BitVec.ofNat 32 (2^(4*i.val+s.val)))) := by
      rw [hrot]
      exact hpos
    exact real_oneHot_implies_exact_local k i r s hpos'

/-! ## 4. Global support is the disjoint union of its eight exact blocks. -/

private def tripleActual (k : Word) : Finset Triple :=
  Finset.univ.filter (fun p : Triple => 0 < fastOneHotDDT k (srcBit p.1 p.2.1) (dstBit p.1 p.2.2))

private def tripleExact (k : Word) : Finset Triple :=
  Finset.univ.filter
    (fun p : Triple =>
      localPotential p.1 (wordDigits k p.1) (exactCarryFlag k p.1) p.2.1 p.2.2 = true)

private theorem src_injective (i : Fin 8) : Function.Injective (srcBit i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [srcBit] at hh
  omega

private theorem dst_injective (i : Fin 8) : Function.Injective (dstBit i) := by
  intro r s h
  apply Fin.ext
  have hh := congrArg (fun z : Fin 32 => (z.val + 21) % 32) h
  dsimp [dstBit] at hh
  omega

private theorem tripleActual_card_eq_real (k : Word) :
    (tripleActual k).card = (fastPositiveCells k).card := by
  classical
  apply Finset.card_bij (fun p _ => (srcBit p.1 p.2.1, dstBit p.1 p.2.2))
  · intro ⟨i, r, s⟩ hp
    simpa only [tripleActual, fastPositiveCells, Finset.mem_filter, Finset.mem_univ, true_and] using
      hp
  · intro ⟨i, r, s⟩ _ ⟨i', r', s'⟩ _ heq
    have hs := congrArg Prod.fst heq
    have hd := congrArg Prod.snd heq
    have hi : i = i' := by
      apply Fin.ext
      have hh := congrArg (fun v : Fin 32 => v.val / 4) hs
      dsimp [srcBit] at hh
      omega
    subst i'
    have hr : r = r' := src_injective i hs
    have ht : s = s' := dst_injective i hd
    subst r'
    subst s'
    rfl
  · intro ⟨j, ell⟩ hp
    have hr : 0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (BitVec.ofNat 32 (2 ^ ell.val)) := by
      rw [← fastOneHotDDT_correct]
      exact (Finset.mem_filter.mp hp).2
    have hsame := oneHot_positive_implies_same_nibble k j ell hr
    let i : Fin 8 := ⟨j.val / 4, by omega⟩
    let r : Fin 4 := ⟨j.val % 4, by omega⟩
    let s : Fin 4 := ⟨((ell.val + 21) % 32) % 4, by omega⟩
    have hj : srcBit i r = j := by
      apply Fin.ext
      dsimp [srcBit, i, r]
      omega
    have he : dstBit i s = ell := by
      apply Fin.ext
      dsimp [dstBit, i, s] at *
      omega
    refine ⟨(i, (r, s)), ?_, ?_⟩
    · simp only [tripleActual, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hj, he]
      exact (Finset.mem_filter.mp hp).2
    · exact Prod.ext hj he

private theorem tripleExact_card (k : Word) : (tripleExact k).card = exactLocalSupportCount k := by
  let block (i : Fin 8) : Finset Local :=
    Finset.univ.filter
      (fun rs : Local => localPotential i (wordDigits k i) (exactCarryFlag k i) rs.1 rs.2 = true)
  have hset :
    tripleExact k =
      (Finset.univ : Finset (Fin 8)).biUnion (fun i => ({i} : Finset (Fin 8)) ×ˢ block i) := by
    ext ⟨i, rs⟩
    simp [tripleExact, block]
  rw [hset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    simp [block, localPotentialCount]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro ⟨u, rs⟩ hu hv
    have hui : u = i := Finset.mem_singleton.mp (Finset.mem_product.mp hu).1
    have huj : u = j := Finset.mem_singleton.mp (Finset.mem_product.mp hv).1
    exact hij (hui.symm.trans huj)

/-- COMPLETENESS: the sharp local predictor is a genuinely exact
    fixed-key one-hot support formula. -/
theorem fixedKey_realSupport_eq_exactLocal (k : Word) :
    (fastPositiveCells k).card = exactLocalSupportCount k := by
  rw [← tripleActual_card_eq_real]
  have hsets : tripleActual k = tripleExact k := by
    ext ⟨i,r,s⟩
    simp only [tripleActual, tripleExact, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (localPotential_exact_iff_real k i r s).symm
  rw [hsets]
  exact tripleExact_card k

/-- The same theorem, phrased in the original mathematical DDT. -/
theorem real_oneHot_support_eq_exactLocal (k : Word) :
    ((Finset.univ : Finset Cell).filter (fun p : Cell =>
      0 < xorDDT_g k
        (BitVec.ofNat 32 (2 ^ p.1.val))
        (BitVec.ofNat 32 (2 ^ p.2.val)))).card =
      exactLocalSupportCount k := by
  rw [← fastPositiveCells_eq_real]
  exact fixedKey_realSupport_eq_exactLocal k

/-- The old ceiling becomes an exact bound on the new local model. -/
theorem exactLocalSupportCount_le_72 (k : Word) :
    exactLocalSupportCount k ≤ 72 := by
  rw [← fixedKey_realSupport_eq_exactLocal]
  exact every_key_at_most_72 k

/-- Characterize attaining the sharp global maximum entirely by the
    eight small, key-dependent local tables. -/
theorem realSupport_eq_72_iff_local (k : Word) :
    (fastPositiveCells k).card = 72 ↔ exactLocalSupportCount k = 72 := by
  rw [fixedKey_realSupport_eq_exactLocal]

example : (fastPositiveCells (0#32)).card = 59 := by
  rw [fixedKey_realSupport_eq_exactLocal]
  decide +kernel

example : (fastPositiveCells candidate72Key).card = 72 :=
  candidate72Key_has_72_cells

end Magma.OneHotExactLocalSupportCompleteness
