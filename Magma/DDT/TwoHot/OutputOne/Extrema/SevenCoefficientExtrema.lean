module

public import Magma.DDT.TwoHot.OutputOne.Exact.SevenQuantitativeClosure
import all Init.Data.Range.Basic

@[expose] public section

/-!
Exact extrema of the 7 potentially positive two-hot / output-1
coefficients of the 32-bit Magma round function.

No change to existing `private` declarations.

The numerical certificates are restricted to the six relevant nibble-5
input differences and to the two local 4-bit S-box/carry steps.

-/

open scoped BigOperators

namespace Magma.TwoHotSevenCoefficientExtrema

open Magma
open Magma.CarryAutomaton
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotOutputOneSevenExactCounts
open Magma.TwoHotUniformTwoDigitKernel
open Magma.TwoHotSevenQuantitativeClosure

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

private abbrev Digit :=
  Fin 16

private abbrev Carry :=
  Fin 2

private abbrev B : Nat :=
  16 ^ 5

private def sixDeltas : Finset Digit :=
  {3, 5, 6, 9, 10, 12}

/-- In the six same-nibble cases the local coefficient is EITHER 0 OR 2.
    This is a small finite certificate involving only nibble 5. -/
theorem localFiveCount_binary (q delta : Digit) (c : Carry)
    (hd : delta ∈ sixDeltas) :
    localFiveCount q delta c = 0 ∨ localFiveCount q delta c = 2 := by
  have h : delta = 3 ∨ delta = 5 ∨ delta = 6 ∨
      delta = 9 ∨ delta = 10 ∨ delta = 12 := by
    simpa [sixDeltas] using hd
  rcases h with h | h | h | h | h | h <;>
    subst delta <;> fin_cases q <;> fin_cases c <;> decide

/-- Nibble 6 receives input difference 1. The two computations can
    agree at its output exactly for eight of its sixteen inputs when
    the two incoming carries differ, regardless of key nibble 6. -/
private theorem upper_zero_count (q : Digit) (st : Carry × Carry) :
    (∑ x : Digit,
      let z := sboxCarryStep (6 : Fin 8) q 1 x st
      if z.1 = 0 ∧ z.2.1 = z.2.2 then (1 : Nat) else 0) =
      if st.1 = st.2 then 0 else 8 := by
  rcases st with ⟨c₀, c₁⟩
  fin_cases c₀ <;> fin_cases c₁ <;> fin_cases q <;> decide

/-- The cross-nibble coefficient is completely independent of key nibble 6!
    It is 16 if the nibble-5 key and the incoming carry are in one of
    the listed classes, and zero otherwise. -/
def crossAllowed (q : Digit) (c : Carry) : Prop :=
  (7 ≤ q.val ∧ q.val ≤ 13) ∨
  (q.val = 6 ∧ c = 1) ∨
  (q.val = 14 ∧ c = 0)

instance (q : Digit) (c : Carry) : Decidable (crossAllowed q c) := by
  unfold crossAllowed
  infer_instance

theorem localFiveSixCount_exact (q5 q6 : Digit) (c : Carry) :
    localFiveSixCount q5 q6 c = if crossAllowed q5 c then 16 else 0 := by
  have hcollapse :
    localFiveSixCount q5 q6 c =
      ∑ x5 : Digit,
        let st := sboxCarryStep (5 : Fin 8) q5 8 x5 (c, c)
        if st.1 = 2 ∧ st.2.1 ≠ st.2.2 then 8 else 0 := by
    unfold localFiveSixCount
    apply Finset.sum_congr rfl
    intro x5 _
    let st := sboxCarryStep (5 : Fin 8) q5 8 x5 (c, c)
    change
      (∑ x6 : Digit,
          let z := sboxCarryStep (6 : Fin 8) q6 1 x6 st.2
          if st.1 = 2 ∧ z.1 = 0 ∧ z.2.1 = z.2.2 then (1 : Nat) else 0) =
        if st.1 = 2 ∧ st.2.1 ≠ st.2.2 then 8 else 0
    by_cases h : st.1 = 2
    · simp only [h, true_and]
      rw [upper_zero_count]
      by_cases hc : st.2.1 = st.2.2 <;> simp [hc]
    · simp [h]
  rw [hcollapse]
  fin_cases q5 <;> fin_cases c <;> decide

private theorem prefixK_lt (k : Word) : prefixK k < B := by
  unfold prefixK B
  exact Nat.mod_lt _ (by norm_num)

private theorem sixPair_delta (p : PairBits) (hp : p ∈ sevenPairs) (hn : p ≠ crossPair) :
    wordDigits (twoHot p.1 p.2) (5 : Fin 8) ∈ sixDeltas := by
  simp only [sevenPairs, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h | h | h | h | h
  · subst p; decide
  · subst p; decide
  · subst p; decide
  · subst p; decide
  · subst p; decide
  · subst p; decide
  · subst p; simp [crossPair] at hn

/-! A generic convex-weight argument. No case split on the 20-bit prefix. -/

private theorem weighted_le (K M a b : Nat) (hK : K ≤ B) (ha : a ≤ M) (hb : b ≤ M) :
    (B - K) * a + K * b ≤ B * M := by
  calc
    (B - K) * a + K * b ≤ (B - K) * M + K * M :=
      Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb)
    _ = B * M := by rw [← add_mul, Nat.sub_add_cancel hK]

/-! The only arithmetic facts needed about the closed weights.
    Normalize `B` in *hypotheses as well as the goal*: `omega` cannot
    infer that an opaque numeral abbreviation is 1048576. -/

private theorem weighted_binary_peak (K L a b : Nat) (hK : K < B) (ha : a = 0 ∨ a = L)
    (hb : b = 0 ∨ b = L) (hL : L = 2 ∨ L = 16) :
    (B - K) * a + K * b = B * L ↔ a = L ∧ (K = 0 ∨ b = L) := by
  rcases hL with hL | hL <;> subst L <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp_all [B] <;>
    omega

/-- Numerically scaled equality, without asking omega to understand
    the symbolic abbreviation `B` or a product of two variables. -/
private theorem six_scale (z : Nat) :
    256 * z = 2 ^ 29 ↔ z = B * 2 := by
  norm_num [B]; omega

private theorem cross_scale (z : Nat) : 16 * z = 2 ^ 28 ↔ z = B * 16 := by
  norm_num [B]; omega

/-- Fix a single normal form for the `if` in weightedSevenCount.
    Note that the actual test in the definition is `p = (23,24)`. -/
private theorem six_branch (k : Word) (p : PairBits)
    (hn : p ≠ crossPair) :
    weightedSevenCount k p =
      256 * ((B - prefixK k) *
        localFiveCount (wordDigits k 5)
          (wordDigits (twoHot p.1 p.2) 5) 0 +
        prefixK k * localFiveCount (wordDigits k 5)
          (wordDigits (twoHot p.1 p.2) 5) 1) := by
  have hne : p ≠ ((23 : Fin 32), (24 : Fin 32)) := by
    simpa only [crossPair] using hn
  simp only [weightedSevenCount, ite_eq_right hne]

private theorem cross_branch (k : Word) :
    weightedSevenCount k crossPair =
      16 *
        ((B - prefixK k) * localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0 +
          prefixK k * localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1) := by
  simp only [weightedSevenCount, crossPair, ite_true]

/-- All six same-nibble coefficients are at most 2^29. -/
theorem six_coeff_le_2pow29 (k : Word) (p : PairBits)
    (hp : p ∈ sevenPairs) (hn : p ≠ crossPair) :
    weightedSevenCount k p ≤ 2 ^ 29 := by
  have hdelta := sixPair_delta p hp hn
  have h0 := localFiveCount_binary
    (wordDigits k 5) (wordDigits (twoHot p.1 p.2) 5) 0 hdelta
  have h1 := localFiveCount_binary
    (wordDigits k 5) (wordDigits (twoHot p.1 p.2) 5) 1 hdelta
  have hK := prefixK_lt k
  have hbound := weighted_le (prefixK k) 2
    (localFiveCount (wordDigits k 5)
      (wordDigits (twoHot p.1 p.2) 5) 0)
    (localFiveCount (wordDigits k 5)
      (wordDigits (twoHot p.1 p.2) 5) 1)
    (Nat.le_of_lt hK)
    (by rcases h0 with h | h <;> omega)
    (by rcases h1 with h | h <;> omega)
  rw [six_branch k p hn]
  calc
    256 * ((B - prefixK k) *
        localFiveCount (wordDigits k 5)
          (wordDigits (twoHot p.1 p.2) 5) 0 +
        prefixK k * localFiveCount (wordDigits k 5)
          (wordDigits (twoHot p.1 p.2) 5) 1) ≤
        256 * (B * 2) := Nat.mul_le_mul_left 256 hbound
    _ = 2 ^ 29 := by norm_num [B]

/-- The exceptional cross-nibble coefficient is at most 2^28. -/
theorem cross_coeff_le_2pow28 (k : Word) :
    weightedSevenCount k crossPair ≤ 2 ^ 28 := by
  have hK := prefixK_lt k
  have h0 := localFiveSixCount_exact
    (wordDigits k 5) (wordDigits k 6) 0
  have h1 := localFiveSixCount_exact
    (wordDigits k 5) (wordDigits k 6) 1
  have hb := weighted_le (prefixK k) 16
    (localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0)
    (localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1)
    (Nat.le_of_lt hK)
    (by rw [h0]; split_ifs <;> omega)
    (by rw [h1]; split_ifs <;> omega)
  rw [cross_branch k]
  calc
    16 * ((B - prefixK k) *
        localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0 +
        prefixK k *
        localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1) ≤
      16 * (B * 16) := Nat.mul_le_mul_left 16 hb
    _ = 2 ^ 28 := by norm_num [B]

/-- An exact local criterion for attaining 2^28 at (23,24). -/
theorem cross_coeff_eq_2pow28_iff (k : Word) :
    weightedSevenCount k crossPair = 2 ^ 28 ↔
      crossAllowed (wordDigits k 5) 0 ∧
      (prefixK k = 0 ∨ crossAllowed (wordDigits k 5) 1) := by
  have hK := prefixK_lt k
  have h0 := localFiveSixCount_exact
    (wordDigits k 5) (wordDigits k 6) 0
  have h1 := localFiveSixCount_exact
    (wordDigits k 5) (wordDigits k 6) 1
  have hbinary0 :
      localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0 = 0 ∨
      localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0 = 16 := by
    rw [h0]
    split_ifs <;> simp
  have hbinary1 :
      localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1 = 0 ∨
      localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1 = 16 := by
    rw [h1]
    split_ifs <;> simp
  have hpeak := weighted_binary_peak (prefixK k) 16
    (localFiveSixCount (wordDigits k 5) (wordDigits k 6) 0)
    (localFiveSixCount (wordDigits k 5) (wordDigits k 6) 1)
    hK hbinary0 hbinary1 (Or.inr rfl)
  rw [cross_branch k, cross_scale]
  rw [hpeak, h0, h1]
  simp

/-- The six same-nibble maxima require a maximal local count at carry 0,
    plus a maximal count at carry 1 unless the low 20 key bits vanish. -/
theorem six_coeff_eq_2pow29_iff (k : Word) (p : PairBits)
    (hp : p ∈ sevenPairs) (hn : p ≠ crossPair) :
    weightedSevenCount k p = 2 ^ 29 ↔
      localFiveCount (wordDigits k 5)
        (wordDigits (twoHot p.1 p.2) 5) 0 = 2 ∧
      (prefixK k = 0 ∨ localFiveCount (wordDigits k 5)
        (wordDigits (twoHot p.1 p.2) 5) 1 = 2) := by
  have hdelta := sixPair_delta p hp hn
  have h0 := localFiveCount_binary
    (wordDigits k 5) (wordDigits (twoHot p.1 p.2) 5) 0 hdelta
  have h1 := localFiveCount_binary
    (wordDigits k 5) (wordDigits (twoHot p.1 p.2) 5) 1 hdelta
  have hK := prefixK_lt k
  have hpeak := weighted_binary_peak (prefixK k) 2
    (localFiveCount (wordDigits k 5)
      (wordDigits (twoHot p.1 p.2) 5) 0)
    (localFiveCount (wordDigits k 5)
      (wordDigits (twoHot p.1 p.2) 5) 1)
    hK h0 h1 (Or.inl rfl)
  rw [six_branch k p hn, six_scale]
  exact hpeak

/-- Unconditional real-DDT bound for all 496 ordered input pairs. -/
theorem every_twoHot_coefficient_le_2pow29 (k : Word)
    (p : PairBits) (hij : p.1.val < p.2.val) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) ≤ 2 ^ 29 := by
  rw [all_496_twoHot_exact k p hij]
  by_cases hp : p ∈ sevenPairs
  · simp only [proposedTwoHotClosedCount, ite_eq_left hp]
    by_cases hc : p = crossPair
    · subst p
      exact le_trans (cross_coeff_le_2pow28 k) (by norm_num)
    · exact six_coeff_le_2pow29 k p hp hc
  · simp [proposedTwoHotClosedCount, hp]

/-- Sharpness is witnessed by an ordinary same-nibble pair, not by
    the special (23,24) transition. -/
theorem twoHot_global_maximum_sharp :
    (∀ (k : Word) (p : PairBits), p.1.val < p.2.val →
      xorDDT_g k (twoHot p.1 p.2) (1#32) ≤ 2 ^ 29) ∧
    (∃ (k : Word) (p : PairBits), p.1.val < p.2.val ∧
      xorDDT_g k (twoHot p.1 p.2) (1#32) = 2 ^ 29) := by
  constructor
  · intro k p hp
    exact every_twoHot_coefficient_le_2pow29 k p hp
  · refine ⟨0#32, (20,21), by decide, ?_⟩
    rw [all_496_twoHot_exact (0#32) (20,21) (by decide)]
    decide

/-- Sharp bound for the exceptional cross-nibble pair in the genuine DDT. -/
theorem cross_real_coefficient_le_2pow28 (k : Word) :
    xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) ≤
      2 ^ 28 := by
  rw [all_496_twoHot_exact k (23,24) (by decide)]
  simpa [proposedTwoHotClosedCount, sevenPairs, crossPair]
    using cross_coeff_le_2pow28 k

/-- The exceptional bound is sharp; a low-complexity concrete key
    suffices, independently of the other round words. -/
theorem cross_real_maximum_sharp :
    ∃ k : Word,
      xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) =
        2 ^ 28 := by
  refine ⟨0x00700000#32, ?_⟩
  rw [all_496_twoHot_exact (0x00700000#32) (23,24) (by decide)]
  decide

theorem cross_real_coefficient_eq_2pow28_iff (k : Word) :
    xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) = 2 ^ 28 ↔
      crossAllowed (wordDigits k 5) 0 ∧ (prefixK k = 0 ∨ crossAllowed (wordDigits k 5) 1) := by
  rw [all_496_twoHot_exact k (23, 24) (by decide)]
  simpa [proposedTwoHotClosedCount, sevenPairs, crossPair] using cross_coeff_eq_2pow28_iff k

end Magma.TwoHotSevenCoefficientExtrema
