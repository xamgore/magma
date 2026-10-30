module

import all Init.Data.Range.Basic
public import Magma.Diffan.FeistelDeltaPropagation
public import Magma.Composition.ZeroLeft.ParityCompleteSlice

@[expose] public section

/-!
# Nonconstant corrections in genuine two-round Feistel propagation

The propagation lemma in `FeistelDeltaPropagation` identifies the correction
in the second round as a derivative of `g[k]` at a *real* base point.

Here we show that the derivative in input direction `1#32` cannot be constant
for every 32-bit round key: the certified parity-dependent row has at least two
possible output differences. We also rule out a constant derivative in the
specific even-row DDT symmetry direction `0x00006000` at key zero, using two
concrete input points.

This distinction matters: translation invariance of a marginal DDT row is
not the same as a pointwise translation law of the underlying function.
-/

namespace Magma.DiffanFeistelCorrectionObstructions

open Magma
open Magma.CarryAutomaton
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.OddUnitInput77
open Magma.DiffanFeistelDeltaPropagation

private abbrev Word :=
  V 32

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- A positive DDT count supplies a genuine input realizing its output. -/
private theorem output_of_constant_derivative
    (k d b u : Word)
    (hconst : ∀ x : Word, g k (x ^^^ d) ^^^ g k x = u)
    (hpos : 0 < xorDDT_g k d b) : b = u := by
  unfold xorDDT_g at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hx' := (Finset.mem_filter.mp hx).2
  change g k (x ^^^ d) ^^^ g k x = b at hx'
  exact hx'.symm.trans (hconst x)

private theorem unit_row_positive_iff (k b : Word) :
    0 < xorDDT_g k (1#32) b ↔ b ∈ parityRowSupport k := by
  rw [← one_round_unit_support_exact k]
  simp only [Magma.ZeroLeftColumnTransport.firstRoundSupport, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Output 0x1000 is supported in both parity classes. -/
private theorem first_unit_output_positive (k : Word) :
    0 < xorDDT_g k (1#32) (0x00001000#32) := by
  rw [unit_row_positive_iff]
  by_cases hk : k.toNat % 2 = 0
  · simp only [parityRowSupport, hk, ite_true]
    decide
  · simp only [parityRowSupport, hk, ite_false]
    decide +kernel

/-- Another supported output, distinct from 0x1000, is selected by
    key parity. -/
private theorem second_unit_output_positive (k : Word) :
    0 < xorDDT_g k (1#32)
      (if k.toNat % 2 = 0 then (0x00001800#32) else (0x00002800#32)) := by
  rw [unit_row_positive_iff]
  by_cases hk : k.toNat % 2 = 0
  · simp only [parityRowSupport, hk, ite_true]
    decide
  · simp only [parityRowSupport, hk, ite_false]
    decide +kernel

private theorem second_unit_output_ne_first (k : Word) :
    (if k.toNat % 2 = 0 then (0x00001800#32 : Word) else (0x00002800#32 : Word)) ≠
      (0x00001000#32 : Word) := by
  split_ifs <;> decide

/-- Universal obstruction: for every key, the input-one XOR derivative
    of the real Magma round function is not constant. -/
theorem unit_direction_derivative_nonconstant (k u : Word) :
    ¬ (∀ x : Word, g k (x ^^^ (1#32)) ^^^ g k x = u) := by
  intro hconst
  have hfirst := output_of_constant_derivative k (1#32)
    (0x00001000#32) u hconst (first_unit_output_positive k)
  have hsecond := output_of_constant_derivative k (1#32)
    (if k.toNat % 2 = 0 then (0x00001800#32) else (0x00002800#32))
    u hconst (second_unit_output_positive k)
  exact second_unit_output_ne_first k (hsecond.trans hfirst.symm)

/-- The second-round correction in direction 1 is not a fixed word,
    regardless of the round key. -/
theorem unit_direction_correction_not_uniform (k u : Word) :
    ¬ (∀ mid : Point, secondCorrection k (1#32) mid = u) := by
  intro h
  exact unit_direction_derivative_nonconstant k u
    ((correction_uniform_iff_g_constant_derivative k (1#32) u).mp h)

/-- Each round key admits midpoint pairs with different corrections. -/
theorem unit_direction_correction_has_distinct_values (k : Word) :
    ∃ p q : Point,
      secondCorrection k (1#32) p ≠ secondCorrection k (1#32) q := by
  by_contra! h
  let p : Point := ⟨(0#32, 0#32), (0#32, 0#32)⟩
  exact unit_direction_correction_not_uniform k
    (secondCorrection k (1#32) p) (fun q => (h p q).symm)

/-! ## The DDT symmetry direction 0x6000 is not a pointwise linear structure -/

private def midpointZero : Point :=
  ⟨(0#32, 0#32), (0#32, 0#32)⟩

private def midpointHighNibble : Point :=
  ⟨(0#32, 0x00001000#32), (0#32, 0#32)⟩

/-- These midpoint pairs distinguish the pointwise derivatives in direction
    `0x6000`, which acts as an output translation of the even-key DDT row. -/
theorem zero_key_shift6000_witnesses :
    secondCorrection (0#32) (0x00006000#32) midpointZero =
      (0x01800000#32) ∧
    secondCorrection (0#32) (0x00006000#32) midpointHighNibble =
      (0x07000000#32) := by
  constructor <;> decide

/-- The particular 0x6000 translation symmetry of the even DDT row
    does not arise from a constant XOR derivative of g[0]. -/
theorem zero_key_shift6000_correction_not_uniform (u : Word) :
    ¬ (∀ mid : Point,
      secondCorrection (0#32) (0x00006000#32) mid = u) := by
  intro h
  have ha := h midpointZero
  have hb := h midpointHighNibble
  rw [zero_key_shift6000_witnesses.1] at ha
  rw [zero_key_shift6000_witnesses.2] at hb
  have heq : (0x01800000#32 : Word) = (0x07000000#32 : Word) :=
    ha.trans hb.symm
  exact (by decide : (0x01800000#32 : Word) ≠ (0x07000000#32 : Word)) heq

/-- Equivalent formulation directly in terms of the real g[0] derivative. -/
theorem zero_key_shift6000_derivative_nonconstant (u : Word) :
    ¬ (∀ x : Word,
      g (0#32) (x ^^^ (0x00006000#32)) ^^^ g (0#32) x = u) := by
  intro h
  exact zero_key_shift6000_correction_not_uniform u
    ((correction_uniform_iff_g_constant_derivative
      (0#32) (0x00006000#32) u).mpr h)

end Magma.DiffanFeistelCorrectionObstructions
