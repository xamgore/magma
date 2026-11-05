module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.FirstActiveNibbleInvariant
public import Magma.Differential.ThreeRounds.ThreeRoundMiddleDiagonal
public import Magma.Differential.RoundFunction.OneHotKeyFreeCarryBridge

@[expose] public section

/-!
# Uniform one-hot five-round exclusions from structural Magma lemmas

This module establishes a family of five-round impossible differences
without invoking a SAT solver. Active-nibble positions of one-hot
differences are exactly their bit indices divided by four.
-/

namespace Magma.DiffanOneHotStructuralZero

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFirstActiveNibbleInvariant
open Magma.DiffanOneHotKeyFreeCarryBridge
open Magma.DiffanFiveRoundUniversalSupport
open Magma.DiffanThreeRoundMiddleDiagonal

private abbrev Word :=
  V 32

private def nibbleIndex (i : Fin 32) : Fin 8 :=
  ⟨i.val / 4, by omega⟩

theorem oneHot_firstActiveNibble (i : Fin 32) :
    FirstActiveNibbleAt (oneHotDifference i) (nibbleIndex i) := by
  unfold FirstActiveNibbleAt
  fin_cases i <;> decide

theorem oneHot_ne_zero (i : Fin 32) : oneHotDifference i ≠ (0#32) := by fin_cases i <;> decide

/-- Different first active nibbles cannot connect in five rounds,
    uniformly for every five-word key sequence. -/
theorem fiveRound_oneHot_zero_of_different_nibbles
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j : Fin 32)
    (h : i.val / 4 ≠ j.val / 4) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32)
      (0#32, oneHotDifference j) = 0 := by
  apply fiveRound_zero_of_distinct_firstActiveNibble
    k₀ k₁ k₂ k₃ k₄ (oneHotDifference i) (oneHotDifference j)
    (nibbleIndex i) (nibbleIndex j)
    (oneHot_firstActiveNibble i) (oneHot_firstActiveNibble j)
  exact Fin.ne_of_val_ne h

/-- The diagonal one-hot transition is excluded by the general
    five-round Feistel diagonal obstruction, for all round keys. -/
theorem fiveRound_oneHot_diagonal_zero
    (k₀ k₁ k₂ k₃ k₄ : Word) (i : Fin 32) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32)
      (0#32, oneHotDifference i) = 0 := by
  exact fiveRound_diagonal_impossible
    k₀ k₁ k₂ k₃ k₄ (oneHotDifference i) (oneHot_ne_zero i)

end Magma.DiffanOneHotStructuralZero
