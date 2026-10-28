module

public import Magma.TwoHot.SevenCoefficientExtrema
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Keys attaining the cross-nibble two-hot peak

Exactly 1,879,048,448 actual 32-bit keys attain coefficient 2^28 for
input pair (23, 24) and output difference one. The key classes are counted
through `wordDigitsEquiv` and disjoint Cartesian products of nibble choices.
-/

namespace Magma.TwoHotCrossPeakExactKeyCount

open Magma
open Magma.CarryAutomaton
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenExactCounts
open Magma.TwoHotSevenCoefficientExtrema

private abbrev Word :=
  V 32

private abbrev Q :=
  Fin 16

private abbrev Low :=
  Fin 5 → Q

private abbrev Coords :=
  Low × (Q × (Q × Q))

/-! ## 1. Simplification of the proven extremal key criterion -/

/-- The nibble-6 and nibble-7 key digits do not matter. Exactly the
    seven consecutive nibble-5 values 7,...,13 work for every low prefix;
    value 14 works only when the low 20 key bits are zero. -/
theorem cross_peak_iff_key_class (k : Word) :
    xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) = 2 ^ 28 ↔
      (7 ≤ (wordDigits k 5).val ∧ (wordDigits k 5).val ≤ 13) ∨
      ((wordDigits k 5).val = 14 ∧ prefixK k = 0) := by
  rw [cross_real_coefficient_eq_2pow28_iff]
  -- Simplify the two possible incoming carry values (0 and 1).
  simp [crossAllowed]; omega

/-! ## 2. Arithmetic zero-prefix criterion -/

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
          by_contra hn
          have hpos : 0 < (ds n).val := Nat.pos_of_ne_zero hn
          have hpow : 0 < 16 ^ n := pow_pos (by norm_num) n
          have hmul : 0 < (ds n).val * 16 ^ n := Nat.mul_pos hpos hpow
          change digitPrefixValue ds n + (ds n).val * 16 ^ n = 0 at h
          omega
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

private theorem prefixK_zero_iff_lowDigits_zero (k : Word) :
    prefixK k = 0 ↔ ∀ i : Fin 5, wordDigits k ⟨i.val, by omega⟩ = 0 := by
  have h := digitPrefixValue_zero_iff (wordDigitStream k) 5
  rw [digitPrefixValue_wordDigitStream] at h
  change (prefixK k = 0 ↔ ∀ j : Nat, j < 5 → wordDigitStream k j = 0) at h
  constructor
  · intro hz i
    let j : Fin 8 := ⟨i.val, by omega⟩
    have hj : wordDigitStream k i.val = wordDigits k j := wordDigitStream_at k j
    exact hj ▸ (h.mp hz i.val i.isLt)
  · intro hz
    apply h.mpr
    intro j hj
    let i : Fin 5 := ⟨j, hj⟩
    have hi : wordDigits k ⟨j, by omega⟩ = 0 := hz i
    exact (wordDigitStream_at k ⟨j, by omega⟩).trans hi

/-! ## 3. An explicit 8-nibble coordinate equivalence -/

private def toCoords (d : Fin 8 → Q) : Coords :=
  ((fun i : Fin 5 => d ⟨i.val, by omega⟩), (d 5, (d 6, d 7)))

private def fromCoords (c : Coords) (i : Fin 8) : Q :=
  match i.val with
  | 0 => c.1 0
  | 1 => c.1 1
  | 2 => c.1 2
  | 3 => c.1 3
  | 4 => c.1 4
  | 5 => c.2.1
  | 6 => c.2.2.1
  | _ => c.2.2.2

private def digitCoordsEquiv : (Fin 8 → Q) ≃ Coords where
  toFun := toCoords
  invFun := fromCoords
  left_inv := by
    intro d
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro c
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

private def wordCoordsEquiv : Word ≃ Coords :=
  wordDigitsEquiv.trans digitCoordsEquiv

private theorem wordCoords_apply (k : Word) : wordCoordsEquiv k = toCoords (wordDigits k) := by rfl

/-! ## 4. Small, disjoint Cartesian products of admissible key digits -/

/-- Exactly seven permitted nibble-5 values for an arbitrary prefix. -/
def usualQ5 : Finset Q :=
  Finset.univ.filter (fun q => 7 ≤ q.val ∧ q.val ≤ 13)

theorem usualQ5_card : usualQ5.card = 7 := by decide

private def freeHigh : Finset (Q × Q) :=
  Finset.univ

/-- 16^5 choices of low digits, seven of q5, 16^2 high digits. -/
def usualCoordinates : Finset Coords :=
  (Finset.univ : Finset Low) ×ˢ (usualQ5 ×ˢ freeHigh)

/-- Exactly one low-digit prefix, q5=14, 16^2 high digits. -/
def exceptionalCoordinates : Finset Coords :=
  ({(fun _ => (0 : Q))} : Finset Low) ×ˢ
    ({(14 : Q)} ×ˢ freeHigh)

def maximizingCoordinates : Finset Coords :=
  usualCoordinates ∪ exceptionalCoordinates

/- Avoid `change ...` and elaborator-driven definitional equality against
   `Finset.univ : Finset (Fin 5 → Fin 16)` (2^20 elements).
   Rewriting membership is symbolic and does not enumerate the prefix. -/
private theorem usualCoordinates_mem_iff (c : Coords) :
    c ∈ usualCoordinates ↔ (7 ≤ c.2.1.val ∧ c.2.1.val ≤ 13) := by
  simp only [usualCoordinates, Finset.mem_product, usualQ5, Finset.mem_filter, freeHigh,
    Finset.mem_univ, true_and, and_true]

private theorem exceptionalCoordinates_mem_iff (c : Coords) :
    c ∈ exceptionalCoordinates ↔ (c.2.1.val = 14 ∧ c.1 = (fun _ => (0 : Q))) := by
  simp only [exceptionalCoordinates, Finset.mem_product, freeHigh, Finset.mem_univ,
    Finset.mem_singleton, and_true]
  constructor
  · rintro ⟨hl, hq⟩
    exact ⟨congrArg Fin.val hq, hl⟩
  · rintro ⟨hq, hl⟩
    exact ⟨hl, Fin.ext hq⟩

private theorem maximizingCoordinates_mem_iff (c : Coords) :
    c ∈ maximizingCoordinates ↔
      (7 ≤ c.2.1.val ∧ c.2.1.val ≤ 13) ∨ (c.2.1.val = 14 ∧ c.1 = (fun _ => 0)) := by
  rw [maximizingCoordinates, Finset.mem_union, usualCoordinates_mem_iff,
    exceptionalCoordinates_mem_iff]

private theorem usual_exceptional_disjoint : Disjoint usualCoordinates exceptionalCoordinates := by
  apply Finset.disjoint_left.mpr
  intro c
  rw [usualCoordinates_mem_iff, exceptionalCoordinates_mem_iff]
  omega

theorem usualCoordinates_card : usualCoordinates.card = 1879048192 := by
  simp [usualCoordinates, freeHigh, Finset.card_product, usualQ5_card, Fintype.card_prod]

theorem exceptionalCoordinates_card : exceptionalCoordinates.card = 256 := by
  simp [exceptionalCoordinates, freeHigh, Fintype.card_prod]

theorem maximizingCoordinates_card : maximizingCoordinates.card = 1879048448 := by
  rw [maximizingCoordinates, Finset.card_union_of_disjoint usual_exceptional_disjoint,
    usualCoordinates_card, exceptionalCoordinates_card]

/-! ## 5. Semantic transfer to actual 32-bit round keys -/

private theorem actual_peak_iff_coordinates (k : Word) :
    xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) = 2 ^ 28 ↔
      wordCoordsEquiv k ∈ maximizingCoordinates := by
  rw [cross_peak_iff_key_class, maximizingCoordinates_mem_iff, wordCoords_apply]
  change
    ((7 ≤ (wordDigits k 5).val ∧ (wordDigits k 5).val ≤ 13) ∨
        ((wordDigits k 5).val = 14 ∧ prefixK k = 0)) ↔
      ((7 ≤ (wordDigits k 5).val ∧ (wordDigits k 5).val ≤ 13) ∨
        ((wordDigits k 5).val = 14 ∧
          (fun i : Fin 5 => wordDigits k ⟨i.val, by omega⟩) = (fun _ => 0)))
  constructor
  · intro h
    rcases h with h | ⟨hq, hp⟩
    · exact Or.inl h
    · refine Or.inr ⟨hq, ?_⟩
      funext i
      exact (prefixK_zero_iff_lowDigits_zero k).mp hp i
  · intro h
    rcases h with h | ⟨hq, hp⟩
    · exact Or.inl h
    · refine Or.inr ⟨hq, (prefixK_zero_iff_lowDigits_zero k).mpr ?_⟩
      intro i
      exact congrFun hp i

/-- Real 32-bit round words attaining the exceptional-pair sharp bound. -/
def actualCrossPeakKeys : Finset Word :=
  Finset.univ.filter (fun k =>
    xorDDT_g k (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) = 2 ^ 28)

/-- Exact number of actual maximizing keys, transferred through `wordDigitsEquiv`. -/
theorem actualCrossPeakKeys_card :
    actualCrossPeakKeys.card = 1879048448 := by
  calc
    actualCrossPeakKeys.card = maximizingCoordinates.card := by
      refine Finset.card_equiv wordCoordsEquiv ?_
      intro k
      simpa only [actualCrossPeakKeys, Finset.mem_filter,
        Finset.mem_univ, true_and] using actual_peak_iff_coordinates k
    _ = 1879048448 := maximizingCoordinates_card

end Magma.TwoHotCrossPeakExactKeyCount
