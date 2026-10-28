module

public import Magma.OneHot.SupportHistogramDP
import all Init.Data.Range.Basic

@[expose] public section

/-!
Exact semantic scan for the one-hot DDT support histogram.

The cached `H` and its coefficient certificate are unchanged.

This module establishes the meaning of the automaton state `seen`,
and identifies the score accumulated by scanning the eight key nibbles
with the exact one-hot DDT support count of that 32-bit key.

It deliberately does NOT identify the executable array-based `pushDigit`
with a semantic prefix histogram: that is a separate, still necessary
invariant. Do not state `realHistogram = H` until that bridge is proved.

-/

namespace Magma.OneHotSupportHistogramSemanticScan

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotExactCarryRegimes
open Magma.OneHotExactLocalSupportCompleteness
open Magma.OneHotSupportHistogramDP

private abbrev Word :=
  V 32

private abbrev Q :=
  Fin 16

private abbrev Digits :=
  Fin 8 → Q

/-! ## 1. Characterizing the nonzero lower key prefix. -/

/-- A base-16 prefix is zero exactly when all its digits are zero.
    The statement works for arbitrary finite prefixes and arbitrary
    digit streams, independently of the 32-bit bound. -/
private theorem digitPrefixValue_eq_zero_iff
    (ds : Nat → Q) (n : Nat) :
    digitPrefixValue ds n = 0 ↔ ∀ j : Nat, j < n → ds j = 0 := by
  induction n with
  | zero =>
      simp [digitPrefixValue]
  | succ n ih =>
      constructor
      · intro h j hj
        have hp : digitPrefixValue ds n = 0 := by
          change digitPrefixValue ds n + (ds n).val * 16 ^ n = 0 at h
          omega
        have hd : ds n = 0 := by
          have hv : (ds n).val = 0 := by
            have hpow : 0 < 16 ^ n := pow_pos (by norm_num) _
            change digitPrefixValue ds n + (ds n).val * 16 ^ n = 0 at h
            have hmul : (ds n).val * 16 ^ n = 0 := by omega
            exact (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt hpow)
          exact Fin.ext hv
        by_cases hjn : j < n
        · exact (ih.mp hp) j hjn
        · have hjEq : j = n := by omega
          simpa [hjEq] using hd
      · intro h
        have hp : digitPrefixValue ds n = 0 :=
          ih.mpr (by intro j hj; exact h j (by omega))
        have hd : ds n = 0 := h n (by omega)
        simp [digitPrefixValue, hp, hd]

/-- Whether any key digit strictly below position `n` is nonzero. -/
def seenBefore (d : Digits) (n : Nat) : Bool :=
  decide (∃ j : Fin 8, j.val < n ∧ d j ≠ 0)

/-- The automaton's prefix flag agrees with the EXACT reachable-carry
    regime from the independently proved arithmetic carry theorem. -/
theorem exactCarryFlag_eq_seenBefore (k : Word) (i : Fin 8) :
    exactCarryFlag k i = seenBefore (wordDigits k) i.val := by
  have hz :
      (k.toNat % 16 ^ i.val = 0) ↔
        ∀ j : Nat, j < i.val → wordDigitStream k j = 0 := by
    rw [← digitPrefixValue_wordDigitStream]
    exact digitPrefixValue_eq_zero_iff (wordDigitStream k) i.val
  by_cases hzero : k.toNat % 16 ^ i.val = 0
  · have hall := hz.mp hzero
    have hn : ¬∃ j : Fin 8, j.val < i.val ∧ wordDigits k j ≠ 0 := by
      rintro ⟨j, hj, hne⟩
      apply hne
      rw [← wordDigitStream_at]
      exact hall j.val hj
    simp only [exactCarryFlag, nibbleBase, seenBefore, hn, hzero, ne_eq,
      not_true_eq_false, decide_false]
  · have hex : ∃ j : Fin 8, j.val < i.val ∧ wordDigits k j ≠ 0 := by
      by_contra hn
      have hall : ∀ j : Nat, j < i.val → wordDigitStream k j = 0 := by
        intro j hj
        let u : Fin 8 := ⟨j, by omega⟩
        have hu : wordDigits k u = 0 := by
          by_contra hne
          exact hn ⟨u, hj, hne⟩
        change wordDigitStream k u.val = 0
        rw [wordDigitStream_at]
        exact hu
      exact hzero (hz.mpr hall)
    simp only [exactCarryFlag, nibbleBase, seenBefore, hex, hzero, ne_eq,
      not_false_eq_true, decide_true]

/-! ## 2. The score accumulated by a sequential scan. -/

/-- The exact score and prefix state after processing the first n digits.
    For n>8 the index wraps, but we only invoke n≤8. -/
def scan (d : Digits) : Nat → Bool × Nat
  | 0 => (false, 0)
  | n + 1 =>
      let p := scan d n
      let q := d (Fin.ofNat 8 n)
      (p.1 || decide (q ≠ 0),
       p.2 + digitWeight (Fin.ofNat 8 n) p.1 q)

private theorem seenBefore_succ (d : Digits) (n : Nat) (hn : n < 8) :
    seenBefore d (n + 1) = (seenBefore d n || decide (d (Fin.ofNat 8 n) ≠ 0)) := by
  have hsplit :
    (∃ j : Fin 8, j.val < n + 1 ∧ d j ≠ 0) ↔
      (∃ j : Fin 8, j.val < n ∧ d j ≠ 0) ∨ d (Fin.ofNat 8 n) ≠ 0 := by
    constructor
    · rintro ⟨j, hj, hne⟩
      by_cases hlt : j.val < n
      · exact Or.inl ⟨j, hlt, hne⟩
      · right
        have he : j = Fin.ofNat 8 n := by
          apply Fin.ext
          simp only [Fin.val_ofNat]
          have hmod : n % 8 = n := Nat.mod_eq_of_lt hn
          omega
        simpa [he] using hne
    · rintro (⟨j, hj, hne⟩ | hne)
      · exact ⟨j, by omega, hne⟩
      · exact ⟨Fin.ofNat 8 n, by simp [Nat.mod_eq_of_lt hn], hne⟩
  simp only [seenBefore, hsplit, Bool.decide_or]

/-- The running Boolean state is exactly the mathematical prefix flag. -/
private theorem scan_seen (d : Digits) (n : Nat) (hn : n ≤ 8) :
    (scan d n).1 = seenBefore d n := by
  induction n with
  | zero => simp [scan, seenBefore]
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hi := ih (by omega)
      simpa only [scan, hi] using
        (seenBefore_succ d n hn8).symm

/-- The accumulated score equals the sum of the eight local weights;
    no 32-bit DDT is unfolded here. -/
private theorem scan_score (d : Digits) (n : Nat) (hn : n ≤ 8) :
    (scan d n).2 =
      ∑ j ∈ Finset.range n,
        digitWeight (Fin.ofNat 8 j) (seenBefore d j) (d (Fin.ofNat 8 j)) := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hs := scan_seen d n (by omega)
      simp only [scan, Finset.sum_range_succ]
      rw [ih (by omega), hs]

/-- The program's score, after all eight digits, is precisely the
    already proved exact count of positive DDT cells for the key. -/
theorem scan_score_eq_real_support (k : Word) :
    (scan (wordDigits k) 8).2 = (fastPositiveCells k).card := by
  rw [scan_score (wordDigits k) 8 (le_refl _)]
  rw [Finset.sum_range]
  rw [fixedKey_realSupport_eq_exactLocal]
  unfold exactLocalSupportCount
  apply Finset.sum_congr rfl
  intro i _
  have hi : Fin.ofNat 8 i.val = i := by
    apply Fin.ext
    simp
  rw [hi, digitWeight_correct]
  rw [← exactCarryFlag_eq_seenBefore k i]

/-- A semantic histogram expressed through the scan of the eight key
    digits, without assuming correctness of the cached array transfer. -/
def scanHistogram (n : Nat) : Nat :=
  ((Finset.univ : Finset Digits).filter
    (fun d => (scan d 8).2 = n)).card

/-- Connection of the prefix-scan semantics to actual 32-bit DDTs.
    This is a cardinality theorem, not a numerical experiment. -/
theorem realHistogram_eq_scanHistogram (n : Nat) :
    realHistogram n = scanHistogram n := by
  unfold realHistogram scanHistogram
  refine Finset.card_equiv wordDigitsEquiv ?_
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (fastPositiveCells k).card = n ↔
    (scan (wordDigits k) 8).2 = n
  exact (congrArg (fun v : Nat => v = n) (scan_score_eq_real_support k).symm).to_iff

end Magma.OneHotSupportHistogramSemanticScan
