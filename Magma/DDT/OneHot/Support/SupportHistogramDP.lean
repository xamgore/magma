module

public import Magma.DDT.OneHot.Support.ExactLocalSupportCompleteness
import all Init.Data.Range.Basic

@[expose] public section

/-!
Magma: weighted 2-state DP certificate for the exact one-hot-support
histogram.

The state is `seen`: whether any lower key nibble was nonzero.
At digit i, its score is localPotentialCount i q seen.
After choosing q, newSeen = seen || (q != 0).

This file proves the 256 local score entries by `decide` and certifies
all 73 histogram coefficients by an executable DP, with no full 2^32
key-space enumeration. The separate SEMANTIC bridge between this DP and
`fastPositiveCells` is the next theorem to add; do not treat this
finite certificate alone as that bridge.

The expected values are given as `example` statements only where they
serve as meaningful reproducible numeric regression checks.

-/

namespace Magma.OneHotSupportHistogramDP

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotExactCarryRegimes
open Magma.OneHotExactLocalSupportCompleteness

private abbrev Q :=
  Fin 16

/-- Digit score lookup for the exact prefix-state False. -/
def noCarryScores : List (List Nat) := [
  [10, 8, 9, 7, 8, 5, 8, 7, 7, 7, 8, 6, 7, 4, 7, 8],
  [8, 7, 7, 7, 7, 4, 5, 4, 6, 5, 5, 5, 7, 6, 7, 6],
  [8, 7, 5, 3, 3, 4, 4, 5, 7, 6, 5, 4, 4, 5, 5, 6],
  [7, 5, 6, 4, 4, 5, 5, 4, 5, 3, 5, 4, 6, 7, 7, 6],
  [7, 7, 8, 7, 6, 5, 5, 5, 5, 5, 6, 5, 5, 4, 4, 5],
  [6, 8, 7, 9, 6, 6, 5, 5, 4, 6, 5, 7, 4, 4, 5, 7],
  [5, 4, 5, 4, 3, 4, 5, 5, 4, 3, 4, 3, 2, 3, 4, 6],
  [8, 7, 7, 8, 8, 5, 6, 7, 8, 7, 7, 8, 8, 5, 6, 7]
]

/-- Digit score lookup for the exact prefix-state True. -/
def carryScores : List (List Nat) := [
  [11, 11, 9, 9, 8, 9, 9, 9, 9, 10, 8, 8, 7, 8, 9, 11],
  [8, 8, 8, 8, 7, 6, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8],
  [9, 7, 6, 4, 5, 5, 6, 7, 8, 7, 6, 5, 6, 6, 7, 8],
  [9, 8, 8, 6, 7, 7, 7, 6, 7, 7, 7, 7, 9, 9, 9, 8],
  [9, 9, 10, 9, 7, 7, 8, 8, 7, 7, 8, 8, 6, 6, 7, 9],
  [9, 11, 10, 11, 8, 9, 7, 8, 7, 9, 8, 9, 6, 8, 8, 10],
  [6, 6, 6, 5, 5, 6, 7, 6, 5, 5, 5, 4, 4, 5, 7, 7],
  [9, 8, 9, 8, 9, 6, 7, 8, 9, 8, 9, 8, 9, 6, 7, 8]
]

/-- Exact number of possible local one-hot cells, in the
    specific carry-reachability state. -/
def digitWeight (i : Fin 8) (prefixNonzero : Bool) (q : Q) : Nat :=
  ((if prefixNonzero then carryScores else noCarryScores).getD i.val []).getD q.val 0

/-- All 256 entries are kernel-checked against the earlier exact local
    implementation, not simply assumed from an external script. -/
theorem digitWeight_correct (i : Fin 8) (flag : Bool) (q : Q) :
    digitWeight i flag q = localPotentialCount i q flag := by
  revert i flag q
  decide +kernel

/-! The polynomial is stored as two rows indexed by seen : Bool.
    Each row contains the coefficients for scores 0..72. -/

private def zeroRow : Array Nat :=
  Array.replicate 73 0

private def initial : Array (Array Nat) :=
  #[(zeroRow.set! 0 1), zeroRow]

/-- One weighted transition. Only 2 * 73 * 16 possibilities are visited.
    State update is monotone: once a nonzero key prefix is observed,
    it never returns to `false`. -/
def pushDigit (i : Fin 8) (old : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut next : Array (Array Nat) := #[zeroRow, zeroRow]
  for s in [:2] do
    for t in [:73] do
      let ways := (old.getD s #[]).getD t 0
      if ways != 0 then
        for q in [:16] do
          let newState := if s == 1 || q != 0 then 1 else 0
          let w := digitWeight i (s == 1) (Fin.ofNat 16 q)
          if t + w < 73 then
            let row := next.getD newState zeroRow
            let prev := row.getD (t + w) 0
            next := next.set! newState (row.set! (t + w) (prev + ways))
  return next

/-- Process eight nibbles. Complexity is O(8 * 2 * 73 * 16),
    irrespective of the 2^32 size of the key space. -/
def completed : Array (Array Nat) :=
  (List.finRange 8).foldl (fun acc i => pushDigit i acc) initial

/-- The resulting 73 coefficients for weights 0..72. -/
def histogram : Array Nat :=
  (List.range 73).toArray.map (fun n =>
    (completed.getD 0 zeroRow).getD n 0 +
    (completed.getD 1 zeroRow).getD n 0)

def H (n : Nat) : Nat :=
  histogram.getD n 0

/-- Full 73-coefficient table, calculated by the fast DP. In particular,
    every entry below weight 42 is zero. -/
theorem histogram_certificate :
    histogram.toList =
      List.replicate 42 0 ++
      [
        96, 1568, 12808, 71312, 306276, 1080888, 3256620, 8586292,
        20133464, 42433112, 80916582, 140141776, 220855546, 316914308, 414059766, 492366686,
        532491546, 523249490, 466517464, 376645992, 274596768, 180072760, 105638408, 55018066,
        25168996, 9961242, 3334992, 912388, 192300, 27768, 2016
      ] := by
  decide +kernel

/-- The top coefficient agrees with the independent, already-proved
    key classification at 72. This is a useful cross-check. -/
example : H 72 = 2016 := by
  decide +kernel

/-- Validate the dynamic program at every prefix length: each new
    nibble multiplies the number of represented keys by exactly 16.
    This also checks that the 0..72 storage never drops any path. -/
def afterDigits (n : Nat) : Array (Array Nat) :=
  ((List.finRange 8).take n).foldl (fun acc i => pushDigit i acc) initial

private def tableMass (a : Array (Array Nat)) : Nat :=
  (a.getD 0 zeroRow).toList.sum + (a.getD 1 zeroRow).toList.sum

example :
    (List.range 9).map (fun n => tableMass (afterDigits n)) =
      [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296] := by
  decide +kernel

/-- Mass conservation for the final cached histogram. -/
example : histogram.toList.sum = 2 ^ 32 := by
  rw [histogram_certificate]
  decide +kernel

/-- First raw moment of support size, ready for a later certified mean. -/
example : ((List.range 73).map (fun n => n * H n)).sum = 250123620960 := by
  decide +kernel

/-! ## Semantic reindexing to actual 32-bit round keys.

    This theorem is already unconditional and uses the kernel-proved
    `fixedKey_realSupport_eq_exactLocal` and `wordDigitsEquiv`.
    The NEXT bridge is to identify the digit-fiber cardinality below
    with the cached `H n` computed by `pushDigit`. -/

private abbrev Word :=
  V 32

/-- Cardinality of the REAL fixed-key one-hot DDT support fiber. -/
def realHistogram (n : Nat) : Nat :=
  ((Finset.univ : Finset Word).filter (fun k =>
    (fastPositiveCells k).card = n)).card

/-- Coordinate representation, before using the weighted histogram DP. -/
def digitFiber (n : Nat) : Finset (Fin 8 → Q) :=
  Finset.univ.filter (fun d =>
    exactLocalSupportCount (wordDigitsEquiv.symm d) = n)

/-- This is a genuine cardinality theorem about 32-bit keys.
    No enumeration or computational proof over `Finset Word`. -/
theorem realHistogram_eq_digitFiber (n : Nat) :
    realHistogram n = (digitFiber n).card := by
  unfold realHistogram digitFiber
  refine Finset.card_equiv wordDigitsEquiv ?_
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [wordDigitsEquiv.symm_apply_apply]
  exact (congrArg (fun v : Nat => v = n)
    (fixedKey_realSupport_eq_exactLocal k)).to_iff

end Magma.OneHotSupportHistogramDP
