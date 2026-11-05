module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.GCarryHalfSplit

@[expose] public section

/-!
# A pointwise four-carry-state tensor certificate for genuine g fibers

For an actual 32-bit input x, we split its eight nibbles into two groups
of four. The output of the lower four nibble steps fixes TWO carry bits
at the boundary, and an accept flag. An accepted full eight-step trace
has an accepted low half and an accepted high half. Thus the indicator
of the real fiber of g is a four-term sum of products of block-local
indicators, with NO independence assumption.

The result is stated on two 16-bit blocks represented as four 4-bit
nibbles (`HalfDigits`). This retains the precise local S-box and dual
carry semantics. Transport through an explicit BitVec16 equivalence is
required to apply the earlier BitVec-based `BlockwiseXorCorrelation`
interface directly; this file establishes the Magma pointwise certificate.
-/

namespace Magma.DifanGCarryFiberTensor

open Magma
open Magma.CarryAutomaton
open Magma.DifanGCarryHalfSplit

private abbrev Word :=
  V 32

/-- Four low-order or high-order four-bit digits: one 16-bit block. -/
abbrev HalfDigits := Fin 4 → Fin 16

/-- Low four nibbles of an eight-nibble assignment. -/
def lowDigits (digits : Fin 8 → Fin 16) : HalfDigits :=
  fun i => digits (lowIndex i)

/-- High four nibbles of an eight-nibble assignment. -/
def highDigits (digits : Fin 8 → Fin 16) : HalfDigits :=
  fun i => digits (highIndex i)

/-- Reassemble the full input nibble assignment from two halves. -/
def joinDigits (lo hi : HalfDigits) (i : Fin 8) : Fin 16 :=
  if h : i.val < 4 then lo ⟨i.val, h⟩ else hi ⟨i.val - 4, by omega⟩

@[simp]
theorem joinDigits_low (lo hi : HalfDigits) (i : Fin 4) : joinDigits lo hi (lowIndex i) = lo i := by
  simp [joinDigits, lowIndex, i.isLt]

@[simp]
theorem joinDigits_high (lo hi : HalfDigits) (i : Fin 4) :
    joinDigits lo hi (highIndex i) = hi i := by
  have hn : ¬(i.val + 4 < 4) := by omega
  simp [joinDigits, highIndex, hn]

/-- The split and reassembly are inverse. -/
theorem joinDigits_low_high (digits : Fin 8 → Fin 16) :
    joinDigits (lowDigits digits) (highDigits digits) = digits := by
  funext i
  fin_cases i <;> simp [lowDigits, highDigits, joinDigits, lowIndex, highIndex]

/-- Transition through nibbles 0,1,2,3, including their combined
local-difference acceptance flag. -/
def lowerTrace (key diff target : Fin 8 → Fin 16)
    (input : HalfDigits) : CarryState × Bool :=
  Fin.foldl 4
    (fun acc i =>
      let j := lowIndex i
      let step := sboxCarryStep j (key j) (diff j) (input i) acc.1
      (step.2, acc.2 && decide (step.1 = target j)))
    (((0, 0) : CarryState), true)

/-- Transition through nibbles 4,5,6,7 from a chosen carry and flag. -/
def upperTrace (key diff target : Fin 8 → Fin 16)
    (start : CarryState × Bool) (input : HalfDigits) : CarryState × Bool :=
  Fin.foldl 4
    (fun acc i =>
      let j := highIndex i
      let step := sboxCarryStep j (key j) (diff j) (input i) acc.1
      (step.2, acc.2 && decide (step.1 = target j)))
    start

/-- The REAL eight-step trace equals the two consecutive four-step
traces on the two halves of the input assignment. -/
theorem carryTrace_eq_half_traces
    (key diff target : Fin 8 → Fin 16) (lo hi : HalfDigits) :
    carryTrace key diff target (joinDigits lo hi) =
      upperTrace key diff target (lowerTrace key diff target lo) hi := by
  unfold carryTrace lowerTrace upperTrace
  rfl

/-- A failed lower half cannot be turned into a successful full trace
by any high-half input. The flag accumulates using Boolean AND. -/
theorem upperTrace_false
    (key diff target : Fin 8 → Fin 16)
    (s : CarryState) (hi : HalfDigits) :
    (upperTrace key diff target (s, false) hi).2 = false := by
  unfold upperTrace
  rfl

/-- The low block accepts and exits with precisely this pair of carries. -/
def lowerIndicator (key diff target : Fin 8 → Fin 16)
    (s : CarryState) (lo : HalfDigits) : Nat :=
  if lowerTrace key diff target lo = (s, true) then 1 else 0

/-- The high block accepts when started with the interface carry pair. -/
def upperIndicator (key diff target : Fin 8 → Fin 16)
    (s : CarryState) (hi : HalfDigits) : Nat :=
  if (upperTrace key diff target (s, true) hi).2 = true then 1 else 0

/-- A local successful trace is a FOUR-STATE sum of products of two
independent block predicates, once the carry state is fixed. -/
theorem carryTrace_indicator_eq_four_state
    (key diff target : Fin 8 → Fin 16) (lo hi : HalfDigits) :
    (if (carryTrace key diff target (joinDigits lo hi)).2 = true
      then (1 : Nat) else 0) =
      ∑ s : CarryState,
        lowerIndicator key diff target s lo *
          upperIndicator key diff target s hi := by
  classical
  rw [carryTrace_eq_half_traces]
  rcases hlow : lowerTrace key diff target lo with ⟨s, flag⟩
  cases flag with
  | false =>
      simp [hlow, upperTrace_false, lowerIndicator, upperIndicator]
  | true =>
      simp only [lowerIndicator, hlow, Prod.mk.injEq, and_true]
      rw [Finset.sum_eq_single s]
      · simp [upperIndicator]
      · intro t _ hts
        simp [Ne.symm hts]
      · simp

/-- The output-difference equation of the actual Magma g is equivalent
to an accepted eight-nibble carry trace. -/
theorem true_g_fiber_iff_trace (k d target x : Word) :
    (xor (g k (xor x d)) (g k x) = rot11 target) ↔
      (carryTrace (wordDigits k) (wordDigits d)
        (wordDigits target) (wordDigits x)).2 = true := by
  exact (g_xor_difference_iff_nibbles k d target x).trans
    (carryTrace_iff_nibbleDifferences k d target x).symm

/-- POINTWISE tensorization of the actual XOR-DDT fiber membership.
The four factors are indexed by the real two-carry state after the
lower 16 bits; neither pair of carries is inferred statistically. -/
theorem true_g_fiber_indicator_eq_four_state
    (k d target x : Word) :
    (if xor (g k (xor x d)) (g k x) = rot11 target
      then (1 : Nat) else 0) =
      ∑ s : CarryState,
        lowerIndicator (wordDigits k) (wordDigits d) (wordDigits target)
          s (lowDigits (wordDigits x)) *
        upperIndicator (wordDigits k) (wordDigits d) (wordDigits target)
          s (highDigits (wordDigits x)) := by
  classical
  have hf := true_g_fiber_iff_trace k d target x
  have hpoint :
      (if xor (g k (xor x d)) (g k x) = rot11 target
        then (1 : Nat) else 0) =
      (if (carryTrace (wordDigits k) (wordDigits d)
          (wordDigits target) (wordDigits x)).2 = true
        then (1 : Nat) else 0) := by
    exact if_congr hf rfl rfl
  calc
    (if xor (g k (xor x d)) (g k x) = rot11 target
        then (1 : Nat) else 0) =
      (if (carryTrace (wordDigits k) (wordDigits d)
        (wordDigits target) (wordDigits x)).2 = true
        then (1 : Nat) else 0) := hpoint
    _ = (if (carryTrace (wordDigits k) (wordDigits d)
          (wordDigits target)
          (joinDigits (lowDigits (wordDigits x))
            (highDigits (wordDigits x)))).2 = true
          then (1 : Nat) else 0) := by
            rw [joinDigits_low_high]
    _ = _ := carryTrace_indicator_eq_four_state
      (wordDigits k) (wordDigits d) (wordDigits target)
      (lowDigits (wordDigits x)) (highDigits (wordDigits x))

/-- The same actual g-fiber identity directly as a tensor on the two
16-bit nibble blocks. This is the certified-decomposition hypothesis
needed for a blockwise XOR-correlation, before transporting the blocks
to `BitVec 16` through their digit encodings. -/
theorem true_g_fiber_tensor_on_two_halves
    (k d target : Word) (lo hi : HalfDigits) :
    (if xor (g k (xor (packDigits (joinDigits lo hi)) d))
        (g k (packDigits (joinDigits lo hi))) = rot11 target
      then (1 : Nat) else 0) =
      ∑ s : CarryState,
        lowerIndicator (wordDigits k) (wordDigits d) (wordDigits target) s lo *
          upperIndicator (wordDigits k) (wordDigits d) (wordDigits target) s hi := by
  classical
  have h := true_g_fiber_indicator_eq_four_state
    k d target (packDigits (joinDigits lo hi))
  have hpack : wordDigits (packDigits (joinDigits lo hi)) =
      joinDigits lo hi := wordDigitsEquiv.right_inv (joinDigits lo hi)
  have hlo : lowDigits (joinDigits lo hi) = lo := by
    funext i
    exact joinDigits_low lo hi i
  have hhi : highDigits (joinDigits lo hi) = hi := by
    funext i
    exact joinDigits_high lo hi i
  simpa only [hpack, hlo, hhi] using h

end Magma.DifanGCarryFiberTensor
