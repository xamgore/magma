module
import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.KeyFreeCarryAutomaton

@[expose] public section

namespace Magma.DifanOneHotCarryConcrete

open Magma
open Magma.DifanKeyFreeCarryAutomaton
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect

/-- One of three central-carry obstructions for the 8-to-11 one-hot pair. -/
theorem middle_cannot_8_11_a :
    keyFreePossible (0x00280000#32) (0x00000900#32) = false := by
  decide +kernel

theorem middle_cannot_8_11_b : keyFreePossible (0x00300000#32) (0x00000900#32) = false := by
  decide +kernel

theorem middle_cannot_8_11_c : keyFreePossible (0x00680000#32) (0x00000900#32) = false := by
  decide +kernel

/-- A three-element extreme-support cover would finish the genuine
    five-round 8-to-11 impossibility proof for all round keys. -/
theorem fiveRound_zero_8_11_of_outer_coverage
    (hcover : ∀ c : V 32,
      keyFreePossible (0x00000100#32) c = true →
      keyFreePossible (0x00000800#32) c = true →
      (c = 0x00280000#32 ∨ c = 0x00300000#32 ∨ c = 0x00680000#32))
    (k₀ k₁ k₂ k₃ k₄ : V 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (0x00000100#32, 0#32) (0#32, 0x00000800#32) = 0 := by
  apply fiveRound_zero_of_boolean_keyFree_conflict
  intro c hc
  obtain ⟨hfirst, hmiddle, hlast⟩ := hc
  have hx : Magma.xor (0x00000800#32) (0x00000100#32) = 0x00000900#32 := by
    decide
  rw [hx] at hmiddle
  rcases hcover c hfirst hlast with h | h | h
  · subst c
    simp only [middle_cannot_8_11_a, Bool.false_eq_true] at hmiddle
  · subst c
    simp only [middle_cannot_8_11_b, Bool.false_eq_true] at hmiddle
  · subst c
    simp only [middle_cannot_8_11_c, Bool.false_eq_true] at hmiddle

end Magma.DifanOneHotCarryConcrete
