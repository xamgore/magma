module

public import Magma.TwoHot.OutputOneSevenLocalCandidates
import all Init.Data.Range.Basic
import Magma.OneHot.SilentNibbleStructure

@[expose] public section

/-!
Magma / two-hot input -> output difference 1.
Semantic soundness of the seven-candidate local model and COMPLETE
universal support among the C(32,2)=496 strictly increasing bit pairs.

CRITICAL DOMAIN CORRECTION:
  `twoHot i j = twoHot j i`, so the theorem about seven distinct
  differences MUST restrict to i<j. A previous conditional lemma had
  an unrestricted `hsound : ∀ p, ...` premise, which cannot hold for
  reversed index pairs. This module states and proves the CORRECT
  ordered-pair soundness theorem, and obtains 489 universal zeros.

The hard local fact is that a one-hot difference at bits 25,26,27
cannot be canceled by a difference of the two incoming carries (whose
magnitude is at most one); it is checked by finite 4-bit cases. Bits
28..31 are excluded by the silent nibble 6 and the active nibble 7.

No 32-bit input enumeration, sorry, native_decide, bv_decide, or axioms.
-/

namespace Magma.TwoHotOutputOneSevenSoundness

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OneHotSilentNibbleStructure
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

private def target : Word :=
  0x00200000#32

private theorem target_rot : rot11 target = (1#32) := by decide +kernel

private theorem target5 : wordDigits target (5 : Fin 8) = 2 := by decide +kernel

private theorem target6 : wordDigits target (6 : Fin 8) = 0 := by decide +kernel

private theorem target7 : wordDigits target (7 : Fin 8) = 0 := by decide +kernel

private theorem xorDigit_zero_right (x : Fin 16) : xorDigit x 0 = x := by fin_cases x <;> decide

/-! Prefix equality gives equality of the *actual* carry bits before
    the first active nibble, not an independent-carry assumption. -/

private theorem incomingCarry_congr_prefix (xs ys ks : Nat → Fin 16) (n : Nat)
    (h : ∀ j : Nat, j < n → xs j = ys j) : incomingCarry xs ks n = incomingCarry ys ks n := by
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

private theorem actualCarry5_diagonal (k x : Word) (p : PairBits) (hr : relevantPair p) :
    (wordCarryPair k (twoHot p.1 p.2) x 5).1 = (wordCarryPair k (twoHot p.1 p.2) x 5).2 := by
  have hlow : ∀ u : Fin 8, u.val < 5 → wordDigits (twoHot p.1 p.2) u = 0 := by
    intro u hu
    exact
      twoHot_lower_digits_zero p.1 p.2 hr.1 u
        (by
          have h := hr.2; omega)
  change
    incomingCarry (wordDigitStream x) (wordDigitStream k) 5 =
      incomingCarry (wordDigitStream (xor x (twoHot p.1 p.2))) (wordDigitStream k) 5
  apply incomingCarry_congr_prefix
  intro n hn
  let u : Fin 8 := ⟨n, by omega⟩
  have hd := hlow u (by simpa [u] using hn)
  have hx : wordDigits (xor x (twoHot p.1 p.2)) u = wordDigits x u := by
    rw [wordDigits_xor, hd, xorDigit_zero_right]
  calc
    wordDigitStream x n = wordDigits x u := wordDigitStream_at x u
    _ = wordDigits (xor x (twoHot p.1 p.2)) u := hx.symm
    _ = wordDigitStream (xor x (twoHot p.1 p.2)) n :=
      (wordDigitStream_at (xor x (twoHot p.1 p.2)) u).symm

/-! The following are *index facts* about two bits, checked on 32×32
    pairs. They do not evaluate the round function or DDT. -/

private theorem digit6_below24 (p : PairBits) (hr : relevantPair p) (hj : p.2.val < 24) :
    wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 0 := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

private theorem digit6_at24 (p : PairBits) (hr : relevantPair p) (hj : p.2.val = 24) :
    wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 1 := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

private theorem digit6_at25to27 (p : PairBits) (hr : relevantPair p) (hl : 24 < p.2.val)
    (hu : p.2.val < 28) :
    wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 2 ∨
      wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 4 ∨
      wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 8 := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

private theorem digit6_after27 (p : PairBits) (hr : relevantPair p) (hj : 28 ≤ p.2.val) :
    wordDigits (twoHot p.1 p.2) (6 : Fin 8) = 0 := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

private theorem digit7_after27 (p : PairBits) (hr : relevantPair p) (hj : 28 ≤ p.2.val) :
    wordDigits (twoHot p.1 p.2) (7 : Fin 8) ≠ 0 := by
  rcases p with ⟨i, j⟩
  revert i j
  decide +kernel

/-! A change of a higher (non-LSB) bit in nibble 6 cannot be canceled
    by different incoming carries, regardless of key or input digit.
    The finite check is only 3 × 16 × 16 × 2 × 2 local cases. -/

private theorem no_high_bit_cancel_in_nibble6 (q x : Fin 16) (c₀ c₁ : Fin 2) (d : Fin 16)
    (hd : d = 2 ∨ d = 4 ∨ d = 8) : (sboxCarryStep (6 : Fin 8) q d x (c₀, c₁)).1 ≠ 0 := by
  rcases hd with rfl | rfl | rfl
  all_goals
    revert q x c₀ c₁
    decide +kernel

/-- Extract the actual eight nibble output-difference equations from
    an individual positive DDT entry. No enumeration is performed. -/
private theorem positive_has_word_witness (k d : Word)
    (hp : 0 < xorDDT_g k d (1#32)) :
    ∃ x : Word, ∀ i : Fin 8,
      localSBoxDifference k d x i = wordDigits target i := by
  have hp' : 0 < xorDDT_g k d (rot11 target) := by
    simpa only [target_rot] using hp
  rw [xorDDT_g_eq_nibbles] at hp'
  unfold xorDDT_g_nibbles at hp'
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp'
  refine ⟨x, ?_⟩
  intro i
  exact (localSBoxDifference_eq_iff k d target x i).mpr
    ((Finset.mem_filter.mp hx).2 i)

/-- The semantic core: a real positive two-hot-to-one DDT entry at
    increasing positions has exactly the local carry behavior required
    by `localCandidate`. No hypothesis is made about an abstract model. -/
theorem positive_implies_localCandidate_ordered
    (k : Word) (p : PairBits) (hr : relevantPair p)
    (hp : 0 < xorDDT_g k (twoHot p.1 p.2) (1#32)) :
    localCandidate p = true := by
  let d : Word := twoHot p.1 p.2
  obtain ⟨x, hout⟩ := positive_has_word_witness k d hp
  let c : Fin 2 := (wordCarryPair k d x 5).1
  have hc5 : (wordCarryPair k d x 5).1 =
      (wordCarryPair k d x 5).2 :=
    actualCarry5_diagonal k x p hr
  have hstate5 : wordCarryPair k d x 5 = (c, c) := by
    apply Prod.ext
    · rfl
    · exact hc5.symm
  have hstep5 :
      firstActiveStep p c (wordDigits k 5) (wordDigits x 5) =
        (2, wordCarryPair k d x 6) := by
    have hs := sboxCarryStep_word_correct k d x (5 : Fin 8)
    change sboxCarryStep (5 : Fin 8) (wordDigits k 5) (wordDigits d 5)
      (wordDigits x 5) (wordCarryPair k d x 5) =
        (localSBoxDifference k d x 5, wordCarryPair k d x 6) at hs
    rw [hstate5, hout (5 : Fin 8), target5] at hs
    exact hs
  have hstate6 :
      (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).2 =
        wordCarryPair k d x 6 := congrArg Prod.snd hstep5
  have hstep6 :
      (sboxCarryStep (6 : Fin 8) (wordDigits k 6)
        (wordDigits d 6) (wordDigits x 6)
        (wordCarryPair k d x 6)).1 = 0 := by
    have hs := congrArg Prod.fst
      (sboxCarryStep_word_correct k d x (6 : Fin 8))
    rw [hout (6 : Fin 8), target6] at hs
    exact hs
  have hlocal :
      (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).1 = 2 :=
    congrArg Prod.fst hstep5
  have hcondition :
      (if p.2.val < 24 then
         (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).2.1 =
           (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).2.2
       else if p.2.val = 24 then
         (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).2.1 ≠
           (firstActiveStep p c (wordDigits k 5) (wordDigits x 5)).2.2
       else False) := by
    by_cases hbefore : p.2.val < 24
    · simp only [ite_eq_left hbefore]
      have hd6 : wordDigits d (6 : Fin 8) = 0 :=
        digit6_below24 p hr hbefore
      rw [hd6] at hstep6
      have heq := silent_sbox_zero_forces_diagonal (6 : Fin 8)
        (wordDigits k 6) (wordDigits x 6)
        (wordCarryPair k d x 6).1 (wordCarryPair k d x 6).2 hstep6
      rw [hstate6]
      exact heq
    · simp only [ite_eq_right hbefore]
      by_cases hat24 : p.2.val = 24
      · simp only [ite_eq_left hat24]
        have hd6 : wordDigits d (6 : Fin 8) = 1 :=
          digit6_at24 p hr hat24
        rw [hd6] at hstep6
        have hne : (wordCarryPair k d x 6).1 ≠
            (wordCarryPair k d x 6).2 := by
          intro heq
          have hpair : wordCarryPair k d x 6 =
              ((wordCarryPair k d x 6).1,
               (wordCarryPair k d x 6).1) := by
            apply Prod.ext
            · rfl
            · exact heq.symm
          rw [hpair] at hstep6
          exact (active_sbox_step_nonzero (6 : Fin 8)
            (wordDigits k 6) (1 : Fin 16) (wordDigits x 6)
            (wordCarryPair k d x 6).1 (by decide)) hstep6
        rw [hstate6]
        exact hne
      · simp only [ite_eq_right hat24]
        have hgt24 : 24 < p.2.val := by omega
        by_cases hlt28 : p.2.val < 28
        · have hd6 := digit6_at25to27 p hr hgt24 hlt28
          rcases hd6 with hd6 | hd6 | hd6
          · rw [hd6] at hstep6
            exact False.elim ((no_high_bit_cancel_in_nibble6
              (wordDigits k 6) (wordDigits x 6)
              (wordCarryPair k d x 6).1 (wordCarryPair k d x 6).2
              2 (Or.inl rfl)) hstep6)
          · rw [hd6] at hstep6
            exact False.elim ((no_high_bit_cancel_in_nibble6
              (wordDigits k 6) (wordDigits x 6)
              (wordCarryPair k d x 6).1 (wordCarryPair k d x 6).2
              4 (Or.inr (Or.inl rfl))) hstep6)
          · rw [hd6] at hstep6
            exact False.elim ((no_high_bit_cancel_in_nibble6
              (wordDigits k 6) (wordDigits x 6)
              (wordCarryPair k d x 6).1 (wordCarryPair k d x 6).2
              8 (Or.inr (Or.inr rfl))) hstep6)
        · have hj : 28 ≤ p.2.val := by omega
          have hd6 : wordDigits d (6 : Fin 8) = 0 :=
            digit6_after27 p hr hj
          have hd7 : wordDigits d (7 : Fin 8) ≠ 0 :=
            digit7_after27 p hr hj
          rw [hd6] at hstep6
          have hc6 := silent_sbox_zero_forces_diagonal (6 : Fin 8)
            (wordDigits k 6) (wordDigits x 6)
            (wordCarryPair k d x 6).1 (wordCarryPair k d x 6).2 hstep6
          let c6 : Fin 2 := (wordCarryPair k d x 6).1
          have hpair6 : wordCarryPair k d x 6 = (c6, c6) := by
            apply Prod.ext
            · rfl
            · exact hc6.symm
          have hstep6' := sboxCarryStep_word_correct k d x (6 : Fin 8)
          change sboxCarryStep (6 : Fin 8) (wordDigits k 6) (wordDigits d 6)
            (wordDigits x 6) (wordCarryPair k d x 6) =
              (localSBoxDifference k d x 6, wordCarryPair k d x 7) at hstep6'
          rw [hd6, hpair6, silent_sbox_step_diagonal] at hstep6'
          have hstate7 :
              wordCarryPair k d x 7 =
                (nextCarry (wordDigits x 6) (wordDigits k 6) c6,
                 nextCarry (wordDigits x 6) (wordDigits k 6) c6) :=
            (congrArg Prod.snd hstep6').symm
          have hstep7 := congrArg Prod.fst
            (sboxCarryStep_word_correct k d x (7 : Fin 8))
          change (sboxCarryStep (7 : Fin 8) (wordDigits k 7) (wordDigits d 7)
            (wordDigits x 7) (wordCarryPair k d x 7)).1 =
              localSBoxDifference k d x 7 at hstep7
          rw [hstate7, hout (7 : Fin 8), target7] at hstep7
          exact False.elim ((active_sbox_step_nonzero (7 : Fin 8)
            (wordDigits k 7) (wordDigits d 7) (wordDigits x 7)
            (nextCarry (wordDigits x 6) (wordDigits k 6) c6) hd7)
              hstep7)
  change decide (relevantPair p ∧
    ∃ (cc : Fin 2) (q xx : Fin 16),
      (firstActiveStep p cc q xx).1 = 2 ∧
      (if p.2.val < 24 then
         (firstActiveStep p cc q xx).2.1 =
           (firstActiveStep p cc q xx).2.2
       else if p.2.val = 24 then
         (firstActiveStep p cc q xx).2.1 ≠
           (firstActiveStep p cc q xx).2.2
       else False)) = true
  exact decide_eq_true_eq.mpr ⟨hr,
    ⟨c, wordDigits k 5, wordDigits x 5, hlocal, hcondition⟩⟩

/-- The soundness implication must be restricted to increasing pairs.
    Reversing two input bit positions leaves the two-hot word unchanged. -/
theorem ordered_positive_implies_seven
    (k : Word) (p : PairBits) (hij : p.1.val < p.2.val)
    (hp : 0 < xorDDT_g k (twoHot p.1 p.2) (1#32)) :
    p ∈ sevenPairs := by
  by_cases hfirst : p.1.val / 4 = 5
  · exact (localCandidate_iff_seven p).mp
      (positive_implies_localCandidate_ordered k p ⟨hij, hfirst⟩ hp)
  · have hz := twoHot_output_one_zero_of_not_middle
      k p.1 p.2 hij hfirst
    omega

open scoped Classical

/-- EXACT universal support, among the 496 DISTINCT two-hot differences.
    No conditional soundness hypothesis is used. -/
theorem ordered_universal_support_eq_seven :
    ((Finset.univ : Finset PairBits).filter (fun p =>
      p.1.val < p.2.val ∧
      ∃ k : Word, 0 < xorDDT_g k (twoHot p.1 p.2) (1#32))) =
        sevenPairs := by
  ext p
  constructor
  · intro hp
    obtain ⟨hij, k, hk⟩ := (Finset.mem_filter.mp hp).2
    exact ordered_positive_implies_seven k p hij hk
  · intro hp
    have hij : p.1.val < p.2.val := by
      rcases p with ⟨i, j⟩
      revert i j
      decide +kernel
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hij, seven_pairs_really_reachable p hp⟩

/-- EXACTLY 7 realizable and 489 universally impossible ordered pairs. -/
theorem ordered_universal_support_card :
    ((Finset.univ : Finset PairBits).filter (fun p =>
      p.1.val < p.2.val ∧
      ∃ k : Word, 0 < xorDDT_g k (twoHot p.1 p.2) (1#32))).card = 7 := by
  rw [ordered_universal_support_eq_seven]
  decide +kernel

def universallyImpossibleOrdered : Finset PairBits :=
  ((Finset.univ : Finset PairBits).filter (fun p => p.1.val < p.2.val)) \ sevenPairs

theorem universallyImpossibleOrdered_card : universallyImpossibleOrdered.card = 489 := by
  decide +kernel

/-- All 489 excluded two-bit input differences yield universally zero
    one-round DDT and therefore empty three-round zero-left columns. -/
theorem excluded_twoHot_zero_for_every_key
    (p : PairBits) (hp : p ∈ universallyImpossibleOrdered)
    (k : Word) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) = 0 := by
  have hordered : p.1.val < p.2.val := by
    have h := (Finset.mem_sdiff.mp hp).1
    exact (Finset.mem_filter.mp h).2
  have hnot : p ∉ sevenPairs := (Finset.mem_sdiff.mp hp).2
  by_contra hnonzero
  have hpos : 0 < xorDDT_g k (twoHot p.1 p.2) (1#32) := by
    omega
  exact hnot (ordered_positive_implies_seven k p hordered hpos)

theorem excluded_twoHot_three_round_empty (p : PairBits) (hp : p ∈ universallyImpossibleOrdered)
    (k₀ k₁ k₂ aL : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, 1#32) (0#32, twoHot p.1 p.2) = 0 := by
  have hz := excluded_twoHot_zero_for_every_key p hp k₁
  exact (zeroLeft_column_empty_iff k₀ k₁ k₂ (1#32) (twoHot p.1 p.2)).mpr hz aL

end Magma.TwoHotOutputOneSevenSoundness
