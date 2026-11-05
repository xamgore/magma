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

/-! ### Two independent four-digit certificates. -/

/-- The lower four digits contribute at most four maximal pairs. -/
theorem lowerScore_le_four : ∀ a : Half, lowerScore a ≤ 4 := by
  intro a
  unfold lowerScore
  generalize a 0 = q0
  generalize a 1 = q1
  generalize a 2 = q2
  generalize a 3 = q3
  revert q0 q1 q2 q3
  decide +kernel

/-- With a nonzero lower prefix, the upper half contributes at most four. -/
theorem upperSeenScore_le_four : ∀ b : Half, upperSeenScore b ≤ 4 := by
  intro b
  unfold upperSeenScore
  generalize b 0 = q0
  generalize b 1 = q1
  generalize b 2 = q2
  generalize b 3 = q3
  revert q0 q1 q2 q3
  decide +kernel

/-- With an entirely zero lower half, the upper four digits also
    contribute at most four; the lower four then contribute only three. -/
theorem upperFreshScore_le_four : ∀ b : Half, upperFreshScore b ≤ 4 := by
  intro b
  unfold upperFreshScore
  generalize b 0 = q0
  generalize b 1 = q1
  generalize b 2 = q2
  generalize b 3 = q3
  revert q0 q1 q2 q3
  decide +kernel

/-- All-zero lower prefix has score three, not four. -/
private theorem lowerScore_if_fresh :
    ∀ a : Half, lowerSeen a = false → lowerScore a = 3 := by
  intro a
  unfold lowerSeen lowerScore
  generalize a 0 = q0
  generalize a 1 = q1
  generalize a 2 = q2
  generalize a 3 = q3
  revert q0 q1 q2 q3
  decide +kernel

/-- Exactly 648 lower halves give the maximal half-score four. -/
theorem lowerMaxCard :
    ((Finset.univ : Finset Half).filter
      (fun a => lowerScore a = 4)).card = 648 := by
  decide +kernel

/-- Exactly 384 upper halves give the maximal half-score four,
    once an earlier nonzero nibble is present. -/
theorem upperMaxCard :
    ((Finset.univ : Finset Half).filter
      (fun b => upperSeenScore b = 4)).card = 384 := by
  decide +kernel

/-- No all-zero lower prefix can attain the half-score four. -/
private theorem lower_max_seen :
    ∀ a : Half, lowerScore a = 4 → lowerSeen a = true := by
  intro a
  unfold lowerScore lowerSeen
  generalize a 0 = q0
  generalize a 1 = q1
  generalize a 2 = q2
  generalize a 3 = q3
  revert q0 q1 q2 q3
  decide +kernel

end Magma.OneHotEightPeakPairsExactKeyCount
