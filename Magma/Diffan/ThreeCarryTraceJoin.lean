module

import all Init.Data.Range.Basic
public import Magma.Diffan.MiddleInverseDerivative
public import Magma.Diffan.GCarryFiberTensor

@[expose] public section

/-!
# Three REAL carry traces for the exact five-round inverse join

The pointwise condition for fixed (r,h) is a conjunction of:
* the first g derivative from r and a,
* the middle g^{-1} derivative from h and d=a XOR b,
* the third g derivative from r XOR h and b.

The middle inverse test is represented by the SAME verified FORWARD
carry trace, evaluated at the uniquely reconstructed inverse image
z=(gEquiv k2).symm h.  This is a semantic correctness certificate,
NOT YET a local transfer matrix in the h coordinates: a further
localisation theorem must expose inverse Sboxes, inverse rotation,
and subtraction borrows, then bound the contraction width.
-/

namespace Magma.DiffanThreeCarryTraceJoin

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanMiddleInverseDerivative
open Magma.DiffanFiveRoundImageJoin
open Magma.DiffanGCarryFiberTensor

private abbrev Word :=
  V 32

/-- Trace acceptance for an actual forward g difference, with output
re-rotated to the eight local S-box nibbles. -/
def forwardTraceFiber (key inputDiff outputDiff x : Word) : Prop :=
  (carryTrace
    (wordDigits key) (wordDigits inputDiff)
    (wordDigits (outputDiff.rotateRight 11))
    (wordDigits x)).2 = true

/-- The output rotation aligns the derivative with its nibble carry trace. -/
theorem forward_iff_trace (key inputDiff outputDiff x : Word) :
    gDifference key x inputDiff = outputDiff ↔
      forwardTraceFiber key inputDiff outputDiff x := by
  have h := true_g_fiber_iff_trace key inputDiff
    (outputDiff.rotateRight 11) x
  rw [Magma.Internal.rot11_rotateRight11] at h
  exact h

/-- The middle inverse derivative is also checked by a real carry
trace; only its coordinate system is different. -/
noncomputable def inverseTraceFiber (key outputDiff inputDiff h : Word) : Prop :=
  forwardTraceFiber key inputDiff outputDiff
    (middlePreimage key h)

theorem inverse_iff_trace (key h outputDiff inputDiff : Word) :
    gInverseDifference key h outputDiff = inputDiff ↔
      inverseTraceFiber key outputDiff inputDiff h := by
  rw [← image_middle_iff_inverse key inputDiff outputDiff h]
  exact forward_iff_trace key inputDiff outputDiff (middlePreimage key h)

/-- The three exact derivative predicates share the ACTUAL intermediate c.
All parameters that are fixed appear explicitly. -/
noncomputable def threeTraceCondition (k₁ k₂ k₃ a b c : Word)
    (r h : Word) : Prop :=
  forwardTraceFiber k₁ a c r ∧
  inverseTraceFiber k₂ (xor b a) c h ∧
  forwardTraceFiber k₃ b c (xor h r)

/-- The three derivative constraints agree exactly with three genuine
carry traces. No independence is assumed or used. -/
theorem three_derivatives_iff_three_traces
    (k₁ k₂ k₃ a b c r h : Word) :
    (gDifference k₁ r a = c ∧
      gInverseDifference k₂ h (xor b a) = c ∧
      gDifference k₃ (xor h r) b = c) ↔
      threeTraceCondition k₁ k₂ k₃ a b c r h := by
  unfold threeTraceCondition
  exact and_congr (forward_iff_trace k₁ a c r)
    (and_congr (inverse_iff_trace k₂ h (xor b a) c)
      (forward_iff_trace k₃ b c (xor h r)))

/-- The 5-round exact condition is a triple carry-trace conjunction,
where c is forced by the left word r (not independently sampled). -/
theorem inverseTriple_iff_three_traces
    (k₁ k₂ k₃ a b r h : Word) :
    inverseTripleCondition k₁ k₂ k₃ a b r h ↔
      threeTraceCondition k₁ k₂ k₃ a b (gDifference k₁ r a) r h := by
  unfold inverseTripleCondition
  have hl : gDifference k₁ r a = gDifference k₁ r a := rfl
  have he := three_derivatives_iff_three_traces
    k₁ k₂ k₃ a b (gDifference k₁ r a) r h
  simpa only [hl, true_and] using he

open scoped Classical in
/-- The fully specified three-carry expression; still a mathematical
sum over r,h, intended for a later certified variable-elimination DP. -/
theorem fiveRound_eq_three_carry_traces
    (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    Magma.MultiRoundDDT.xorDDT_rounds 5
        (Magma.DiffanFiveRoundCoreDefect.fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, b) =
      ∑ r : Word, ∑ h : Word,
        if threeTraceCondition k₁ k₂ k₃ a b
            (gDifference k₁ r a) r h
        then (1 : Nat) else 0 := by
  rw [fiveRound_eq_three_inverse_fibers]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact if_congr (inverseTriple_iff_three_traces k₁ k₂ k₃ a b r h)
    rfl rfl

end Magma.DiffanThreeCarryTraceJoin
