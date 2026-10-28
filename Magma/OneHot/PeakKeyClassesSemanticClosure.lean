module

public import Magma.OneHot.PeakKeyClasses
import all Init.Data.Range.Basic

@[expose] public section

/-!
Standalone semantic closure for the peak-key classification.

Proves, WITHOUT EXTRA HYPOTHESES:
  ¬hasPeakCoefficient k ↔ wordCoordinatesEquiv k ∈ noPeakCoordinates
  card {k : V 32 | hasPeakCoefficient k} = 4049764096

-/

namespace Magma.OneHotPeakKeyClasses

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeBridge
open Magma.OneHotExactCoefficientGlobalMaximum
open Magma.OneHotActiveNibbleNecessary

/-! ## 1. A zero lower prefix is exactly a sequence of zero nibbles. -/

private theorem digitPrefixValue_zero_iff (ds : Nat → Q) (n : Nat) :
    digitPrefixValue ds n = 0 ↔ ∀ j : Nat, j < n → ds j = 0 := by
  induction n with
  | zero => simp [digitPrefixValue]
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
      by_cases hn : j < n
      · exact (ih.mp hp) j hn
      · have hjn : j = n := by omega
        simpa [hjn] using hd
    · intro h
      have hp : digitPrefixValue ds n = 0 :=
        ih.mpr
          (by
            intro j hj; exact h j (by omega))
      have hd : ds n = 0 := h n (by omega)
      simp [digitPrefixValue, hp, hd]

theorem keyPrefix_zero_iff_all_lower (k : Word) (i : Fin 8) :
    keyPrefix k i = 0 ↔ ∀ j : Fin 8, j.val < i.val → wordDigits k j = 0 := by
  have h := digitPrefixValue_zero_iff (wordDigitStream k) i.val
  rw [digitPrefixValue_wordDigitStream] at h
  change (k.toNat % 16 ^ i.val = 0) ↔ _
  rw [h]
  constructor
  · intro hh j hj
    rw [← wordDigitStream_at]
    exact hh j.val hj
  · intro hh j hj
    let u : Fin 8 := ⟨j, by omega⟩
    change wordDigitStream k u.val = 0
    rw [wordDigitStream_at]
    exact hh u hj

private def lowNoPeak (d : Fin 8 → Q) : Prop :=
  d 0 ∉ a0 ∧
    (if d 0 = 0 then d 1 ∉ a1 else d 1 ∉ b1) ∧ (if d 0 = 0 ∧ d 1 = 0 then d 2 ∉ a2 else d 2 ∉ b2)

private def highNoPeak (d : Fin 8 → Q) : Prop :=
  d 3 ∉ b3 ∧ d 4 ∉ b4 ∧ d 6 ∉ b6 ∧ d 7 ∉ b7

/-! ## 2. The coordinate predicate is exactly the eight local tests. -/

private theorem lowNoPeak_iff_noPeakPrefix (d : Fin 8 → Q) :
    lowNoPeak d ↔ (d 0, d 1, d 2) ∈ noPeakPrefix := by
  have ha0 : (0 : Q) ∉ a0 := by decide
  have ha1 : (0 : Q) ∉ a1 := by decide
  have ha2 : (0 : Q) ∈ a2 := by decide
  by_cases h0 : d 0 = 0
  · by_cases h1 : d 1 = 0
    · simp [lowNoPeak, noPeakPrefix, avoid, avoidNonzero, h0, h1, ha0, ha1, ha2]
    · simp [lowNoPeak, noPeakPrefix, avoid, avoidNonzero, h0, h1, ha0, eq_comm]
  · simp [lowNoPeak, noPeakPrefix, avoid, avoidNonzero, h0, eq_comm]

private theorem highNoPeak_iff_noPeakHigh (d : Fin 8 → Q) :
    highNoPeak d ↔ (d 3, d 4, d 5, d 6, d 7) ∈ noPeakHigh := by
  simp [highNoPeak, noPeakHigh, avoid, Finset.mem_product]

private theorem lowNoPeak_has_nonzero (d : Fin 8 → Q) (h : lowNoPeak d) :
    d 0 ≠ 0 ∨ d 1 ≠ 0 ∨ d 2 ≠ 0 := by
  by_contra hn
  have h0 : d 0 = 0 := by
    by_contra hx
    exact hn (Or.inl hx)
  have h1 : d 1 = 0 := by
    by_contra hx
    exact hn (Or.inr (Or.inl hx))
  have h2 : d 2 = 0 := by
    by_contra hx
    exact hn (Or.inr (Or.inr hx))
  have ha2 : (0 : Q) ∈ a2 := by decide
  simp [lowNoPeak, h0, h1, h2, ha2] at h

/-! ## 3. Local winning condition for ANY real key. -/

private theorem not_hasPeakLocal_iff_digit_constraints (k : Word) :
    ¬hasPeakLocal k ↔ lowNoPeak (wordDigits k) ∧ highNoPeak (wordDigits k) := by
  let d : Fin 8 → Q := wordDigits k
  have h0 : keyPrefix k 0 = 0 := by simp [keyPrefix, lowBase, Nat.mod_one]
  have h1 : keyPrefix k 1 = 0 ↔ d 0 = 0 := by
    rw [keyPrefix_zero_iff_all_lower]
    constructor
    · intro h; exact h 0 (by decide)
    · intro h j hj
      have he : j = (0 : Fin 8) := Fin.ext (by omega)
      simpa [he] using h
  have h2 : keyPrefix k 2 = 0 ↔ d 0 = 0 ∧ d 1 = 0 := by
    rw [keyPrefix_zero_iff_all_lower]
    constructor
    · intro h
      exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · rintro ⟨h₀, h₁⟩ j hj
      have hor : j = (0 : Fin 8) ∨ j = (1 : Fin 8) := by
        by_cases hz : j.val = 0
        · exact Or.inl (Fin.ext hz)
        · exact Or.inr (Fin.ext (by omega))
      rcases hor with he | he
      · simpa [he] using h₀
      · simpa [he] using h₁
  have hpHigh (h : lowNoPeak d) (i : Fin 8) (hi : 3 ≤ i.val) : keyPrefix k i ≠ 0 := by
    intro hz
    have hall := (keyPrefix_zero_iff_all_lower k i).mp hz
    have h0z : d 0 = 0 := hall 0 (by omega)
    have h1z : d 1 = 0 := hall 1 (by omega)
    have h2z : d 2 = 0 := hall 2 (by omega)
    rcases lowNoPeak_has_nonzero d h with hh | hh | hh
    · exact hh h0z
    · exact hh h1z
    · exact hh h2z
  constructor
  · intro hn
    have hf (i : Fin 8) :
      ¬(if keyPrefix k i = 0 then wordDigits k i ∈ zeroPeakClass i
        else wordDigits k i ∈ bothPeakClass i) := by
      intro hi
      exact hn ⟨i, hi⟩
    have l0 : d 0 ∉ a0 := by simpa [d, h0, a0_correct] using hf 0
    have l1 : (if d 0 = 0 then d 1 ∉ a1 else d 1 ∉ b1) := by
      by_cases hz : d 0 = 0
      · have hh : keyPrefix k 1 = 0 := h1.mpr hz
        simpa [d, hz, hh, a1_correct] using hf 1
      · have hh : keyPrefix k 1 ≠ 0 := fun hh => hz (h1.mp hh)
        simpa [d, hz, hh, b1_correct] using hf 1
    have l2 : (if d 0 = 0 ∧ d 1 = 0 then d 2 ∉ a2 else d 2 ∉ b2) := by
      by_cases hz : d 0 = 0 ∧ d 1 = 0
      · have hh : keyPrefix k 2 = 0 := h2.mpr hz
        simpa [d, hz, hh, a2_correct] using hf 2
      · have hh : keyPrefix k 2 ≠ 0 := fun hh => hz (h2.mp hh)
        simpa [d, hz, hh, b2_correct] using hf 2
    have hlow : lowNoPeak d := ⟨l0, l1, l2⟩
    have h3 := hpHigh hlow 3 (by decide)
    have h4 := hpHigh hlow 4 (by decide)
    have h5 := hpHigh hlow 5 (by decide)
    have h6 := hpHigh hlow 6 (by decide)
    have h7 := hpHigh hlow 7 (by decide)
    have hh3 : d 3 ∉ b3 := by simpa [d, h3, b3_correct] using hf 3
    have hh4 : d 4 ∉ b4 := by simpa [d, h4, b4_correct] using hf 4
    have hh6 : d 6 ∉ b6 := by simpa [d, h6, b6_correct] using hf 6
    have hh7 : d 7 ∉ b7 := by simpa [d, h7, b7_correct] using hf 7
    exact ⟨hlow, ⟨hh3, hh4, hh6, hh7⟩⟩
  · rintro ⟨hlow, hhigh⟩ ⟨i, hi⟩
    have hh3 := hpHigh hlow 3 (by decide)
    have hh4 := hpHigh hlow 4 (by decide)
    have hh5 := hpHigh hlow 5 (by decide)
    have hh6 := hpHigh hlow 6 (by decide)
    have hh7 := hpHigh hlow 7 (by decide)
    rcases hlow with ⟨l0, l1, l2⟩
    rcases hhigh with ⟨h3, h4, h6, h7⟩
    fin_cases i
    · simp [h0, a0_correct] at hi
      exact l0 hi
    · by_cases hz : d 0 = 0
      · have hk : keyPrefix k 1 = 0 := h1.mpr hz
        simp [hk, a1_correct] at hi
        have hl1 : d 1 ∉ a1 := by
          change (if d 0 = 0 then d 1 ∉ a1 else d 1 ∉ b1) at l1
          simpa only [ite_eq_left hz] using l1
        exact hl1 hi
      · have hk : keyPrefix k 1 ≠ 0 := fun hh => hz (h1.mp hh)
        simp [hk, b1_correct] at hi
        have hl1 : d 1 ∉ b1 := by
          change (if d 0 = 0 then d 1 ∉ a1 else d 1 ∉ b1) at l1
          simpa only [ite_eq_right hz] using l1
        exact hl1 hi
    · by_cases hz : d 0 = 0 ∧ d 1 = 0
      · have hk : keyPrefix k 2 = 0 := h2.mpr hz
        simp [hk, a2_correct] at hi
        have hl2 : d 2 ∉ a2 := by
          change (if d 0 = 0 ∧ d 1 = 0 then d 2 ∉ a2 else d 2 ∉ b2) at l2
          simpa only [ite_eq_left hz] using l2
        exact hl2 hi
      · have hk : keyPrefix k 2 ≠ 0 := fun hh => hz (h2.mp hh)
        simp [hk, b2_correct] at hi
        have hl2 : d 2 ∉ b2 := by
          change (if d 0 = 0 ∧ d 1 = 0 then d 2 ∉ a2 else d 2 ∉ b2) at l2
          simpa only [ite_eq_right hz] using l2
        exact hl2 hi
    · simp [hh3, b3_correct] at hi
      exact h3 hi
    · simp [hh4, b4_correct] at hi
      exact h4 hi
    · have hnone : bothPeakClass (5 : Fin 8) = ∅ := by simpa [b5] using b5_correct
      simp [hh5, hnone] at hi
    · simp [hh6, b6_correct] at hi
      exact h6 hi
    · simp [hh7, b7_correct] at hi
      exact h7 hi

/-! ## 4. Unconditional theorem for actual 32-bit keys. -/

theorem no_peak_iff_coordinates (k : Word) :
    (¬hasPeakCoefficient k) ↔ wordCoordinatesEquiv k ∈ noPeakCoordinates := by
  rw [hasPeakCoefficient_iff_local]
  rw [not_hasPeakLocal_iff_digit_constraints]
  rw [lowNoPeak_iff_noPeakPrefix, highNoPeak_iff_noPeakHigh]
  change
    _ ↔
      ((wordDigits k 0, wordDigits k 1, wordDigits k 2),
          (wordDigits k 3, wordDigits k 4, wordDigits k 5, wordDigits k 6, wordDigits k 7)) ∈
        noPeakPrefix ×ˢ noPeakHigh
  rw [Finset.mem_product]

open scoped Classical in
theorem actual_peak_key_count :
    ((Finset.univ : Finset Word).filter hasPeakCoefficient).card = 4049764096 := by
  exact actual_peak_key_count_of_coordinate_characterization no_peak_iff_coordinates

end Magma.OneHotPeakKeyClasses
