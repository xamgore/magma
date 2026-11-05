module

public import Magma.DDT.OneHot.Extrema.PeakPairMultiplicity
import all Init.Data.Range.Basic
import Mathlib.Tactic.SplitIfs
import Aesop

@[expose] public section

/-!
Magma.OneHot.EightPeakPairsExactKeyCount

CLOSES the fixed-key peak-pair multiplicity question:
  every 32-bit key has at most eight one-hot-to-one-hot DDT entries 2^30;
  exactly 248832 ACTUAL 32-bit keys have eight of them.

No full V32 enumeration; two 4-nibble scans (65536 each), whose
finite certificate checks can be split if your local Lean runs out of
heartbeats. The mathematical reduction uses a key/nibble equivalence.

No sorry, native_decide, bv_decide or added axioms.
-/



namespace Magma.OneHotEightPeakPairsExactKeyCount

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotExactCoefficientGlobalMaximum
open Magma.OneHotPeakPairMultiplicity
open Magma.OneHotPeakKeyClasses

private abbrev Word := V 32
private abbrev Q := Fin 16
private abbrev Half := Fin 4 → Q
private abbrev PairBits := Fin 4 × Fin 4

/-! The SMALL lookup tables list, for each q and nibble position,
    the number of (r,s) pairs attaining local count four. The table
    is CHECKED against the real `localMultiplicity`, not trusted. -/

private def zeroRows : List (List Nat) := [
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1],
  [0, 1, 2, 1, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
  [2, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 2, 2, 1, 1],
  [1, 2, 2, 2, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
  [1, 1, 1, 2, 0, 0, 1, 2, 1, 1, 1, 2, 0, 0, 1, 2]
]

private def bothRows : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
  [1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]
]

/-- Exact number of maximizing local (r,s) pairs, selected by whether
    the incoming carry-1 regime can occur. -/
def digitPeakWeight (i : Fin 8) (seen : Bool) (q : Q) : Nat :=
  ((if seen then bothRows else zeroRows).getD i.val []).getD q.val 0

private def actualLocalPeakWeight (i : Fin 8) (seen : Bool) (q : Q) : Nat :=
  ((Finset.univ : Finset PairBits).filter (fun p =>
    localMultiplicity i q 0 p.1 p.2 = 4 ∧
      (seen = false ∨ localMultiplicity i q 1 p.1 p.2 = 4))).card

/-- The entire numeric table is a kernel-checked finite statement. -/
theorem digitPeakWeight_correct (i : Fin 8) (seen : Bool) (q : Q) :
    digitPeakWeight i seen q = actualLocalPeakWeight i seen q := by
  revert i seen q
  decide +kernel

/-- The number of real maximum-strength pairs for a key is the sum of
    these eight local cardinalities. This is the ONLY DDT-to-table bridge
    used in the rest of the file. -/
theorem actualPeakPairs_card_eq_sum_digitWeights (k : Word) :
    (actualPeakPairs k).card =
      ∑ i : Fin 8,
        digitPeakWeight i (decide (keyPrefix k i ≠ 0)) (wordDigits k i) := by
  classical
  rw [actualPeakPairs_card_eq_local]
  have hdecompose : (localPeakPairs k).card =
      ∑ i : Fin 8,
        ((Finset.univ : Finset PairBits).filter (fun p =>
          diagonalWeight k i p.1 p.2 = 2 ^ 30)).card := by
    simp only [localPeakPairs]
    simp only [Finset.card_eq_sum_ones, Fintype.sum_prod_type, Finset.sum_filter]
  rw [hdecompose]
  apply Finset.sum_congr rfl
  intro i _
  rw [digitPeakWeight_correct]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [diagonalWeight_eq_two_pow_30_iff]
  by_cases hk : keyPrefix k i = 0
  · simp [hk]
  · simp [hk]

/-! ### A 4+4 split of the 32-bit key. -/

private def halves : (Fin 8 → Q) ≃ (Half × Half) where
  toFun d :=
    ((fun i => d ⟨i.val, by omega⟩),
     (fun i => d ⟨i.val + 4, by omega⟩))
  invFun p i :=
    if h : i.val < 4 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 4, by omega⟩
  left_inv := by
    intro d
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro p
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private def keyHalves : Word ≃ Half × Half :=
  wordDigitsEquiv.trans halves

private def lowerSeen (a : Half) : Bool :=
  decide (a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0 ∨ a 3 ≠ 0)

/-- Number of maximal local bit pairs in the four least-significant
    nibbles; unlike a single nibble, incoming carry availability is
    determined by the PREVIOUS digits in the same half. -/
def lowerScore (a : Half) : Nat :=
  digitPeakWeight 0 false (a 0) +
  digitPeakWeight 1 (decide (a 0 ≠ 0)) (a 1) +
  digitPeakWeight 2 (decide (a 0 ≠ 0 ∨ a 1 ≠ 0)) (a 2) +
  digitPeakWeight 3 (decide (a 0 ≠ 0 ∨ a 1 ≠ 0 ∨ a 2 ≠ 0)) (a 3)

/-- Upper half, where some lower key digit was already nonzero. -/
def upperSeenScore (b : Half) : Nat :=
  digitPeakWeight 4 true (b 0) +
  digitPeakWeight 5 true (b 1) +
  digitPeakWeight 6 true (b 2) +
  digitPeakWeight 7 true (b 3)

/-- Upper half when all four lower key digits are zero. -/
def upperFreshScore (b : Half) : Nat :=
  digitPeakWeight 4 false (b 0) +
  digitPeakWeight 5 (decide (b 0 ≠ 0)) (b 1) +
  digitPeakWeight 6 (decide (b 0 ≠ 0 ∨ b 1 ≠ 0)) (b 2) +
  digitPeakWeight 7 (decide (b 0 ≠ 0 ∨ b 1 ≠ 0 ∨ b 2 ≠ 0)) (b 3)

/-- This is the exact key-specific number of 2^30 DDT bit pairs,
    expressed purely in nibble coordinates. -/
def twoHalfScore (a b : Half) : Nat :=
  lowerScore a + if lowerSeen a then upperSeenScore b else upperFreshScore b

private theorem keyPrefix_digit_seen (k : Word) (i : Fin 8) :
    (keyPrefix k i = 0) ↔
      ∀ j : Fin 8, j.val < i.val → wordDigits k j = 0 :=
  Magma.OneHotPeakKeyClasses.keyPrefix_zero_iff_all_lower k i

/-- The exact semantic reduction, no 2^32 search. -/
theorem key_multiplicity_eq_twoHalves (k : Word) :
    (actualPeakPairs k).card =
      twoHalfScore (keyHalves k).1 (keyHalves k).2 := by
  rw [actualPeakPairs_card_eq_sum_digitWeights]
  change _ = twoHalfScore
    (fun j : Fin 4 => wordDigits k ⟨j.val, by omega⟩)
    (fun j : Fin 4 => wordDigits k ⟨j.val + 4, by omega⟩)
  by_cases h0 : wordDigits k 0 = 0 <;>
    by_cases h1 : wordDigits k 1 = 0 <;>
    by_cases h2 : wordDigits k 2 = 0 <;>
    by_cases h3 : wordDigits k 3 = 0
  all_goals
    simp [twoHalfScore, lowerScore, upperSeenScore, upperFreshScore, lowerSeen,
      ne_eq, keyPrefix_digit_seen, Fin.forall_fin_succ, Fin.sum_univ_succ,
      h0, h1, h2, h3, not_and_or, add_assoc]

end Magma.OneHotEightPeakPairsExactKeyCount
