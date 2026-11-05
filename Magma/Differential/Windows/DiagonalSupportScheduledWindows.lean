module

import all Init.Data.Range.Basic
public import Magma.Differential.ThreeRounds.ThreeRoundMiddleDiagonal
public import Diffan.Composition.ScheduledConstraints

@[expose] public section

/-!
# Exact diagonal support and master-key windows

The already certified three-round product factorization immediately gives an
exact support criterion. The middle key is absent from that criterion.
We instantiate it with contiguous ordinary Magma-round windows obtained
from ONE master key, preserving any repeated subkeys in the actual schedule.

For every five-round window in the 32-round schedule, the nonzero
diagonal (a,0) → (0,a) is impossible. This is a statement about the
five-round G subchain; it is NOT a claim about the final GStar representation
or about the full 32-round cipher.
-/

namespace Magma.DiffanDiagonalSupportScheduledWindows

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundMiddleDiagonal

private abbrev Word :=
  V 32

/-- On the middle-diagonal slice, support is EXACTLY the intersection of
    the first and last round-function DDT supports. -/
theorem threeRound_diagonal_support_iff
    (k₀ k₁ k₂ aL aR bR : Word) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (aR, bR) ↔
      0 < xorDDT_g k₀ aR aL ∧ 0 < xorDDT_g k₂ aR bR := by
  rw [threeRound_middleDiagonal_factorization]
  constructor
  · intro h
    exact ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩
  · rintro ⟨h₀, h₂⟩
    exact Nat.mul_pos h₀ h₂

/-- A nonzero middle-diagonal input-right difference cannot produce
    zero input-left difference, for ANY round keys. -/
theorem threeRound_diagonal_impossible_zero_inputLeft
    (k₀ k₁ k₂ aR bR : Word) (ha : aR ≠ (0#32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (0#32, aR) (aR, bR) = 0 := by
  rw [threeRound_middleDiagonal_factorization,
    xorDDT_g_zero_output_of_nonzero k₀ aR ha, zero_mul]

/-- The symmetric forbidden family: nonzero aR cannot produce zero
    output-right difference when the output-left equals aR. -/
theorem threeRound_diagonal_impossible_zero_outputRight
    (k₀ k₁ k₂ aL aR : Word) (ha : aR ≠ (0#32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (aR, 0#32) = 0 := by
  rw [threeRound_middleDiagonal_factorization,
    xorDDT_g_zero_output_of_nonzero k₂ aR ha, mul_zero]

/-- The three-round window starting at `start` (0-based) of the actual
    256-bit master-key schedule. Valid starts are 0,...,29. -/
def scheduledThreeKeys (master : V 256) (start : Fin 30) : Fin 3 → Word :=
  fun i => roundKey master ⟨start.val + i.val, by omega⟩

private theorem scheduledThreeKeys_eq (master : V 256) (start : Fin 30) :
    scheduledThreeKeys master start =
      threeRoundKeys (roundKey master ⟨start.val, by omega⟩)
        (roundKey master ⟨start.val + 1, by omega⟩)
        (roundKey master ⟨start.val + 2, by omega⟩) := by
  funext i
  fin_cases i <;> rfl

/-- Actual master-key condition for support. This is a conjunction
    of constraints pulled back along the real Magma schedule; no
    independent round-key variables are quantified. -/
def diagonalConstraintAt (start : Fin 30) (aL aR bR : Word) :
    Diffan.KeyConstraint (V 256) :=
  Diffan.KeyConstraint.intersect
    (Diffan.KeyConstraint.atStep roundKey ⟨start.val, by omega⟩
      (fun k : Word => 0 < xorDDT_g k aR aL))
    (Diffan.KeyConstraint.atStep roundKey ⟨start.val + 2, by omega⟩
      (fun k : Word => 0 < xorDDT_g k aR bR))

/-- Exact characterization of the diagonal's support for ALL 30
    consecutive ordinary three-round windows of a 32-round schedule. -/
theorem scheduledThree_diagonal_support_iff
    (master : V 256) (start : Fin 30) (aL aR bR : Word) :
    0 < xorDDT_rounds 3 (scheduledThreeKeys master start)
      (aL, aR) (aR, bR) ↔
    diagonalConstraintAt start aL aR bR master := by
  rw [scheduledThreeKeys_eq]
  exact threeRound_diagonal_support_iff
    (roundKey master ⟨start.val, by omega⟩)
    (roundKey master ⟨start.val + 1, by omega⟩)
    (roundKey master ⟨start.val + 2, by omega⟩)
    aL aR bR

/-- Every consecutive five-round subchain of the 32-round schedule.
    Starts are 0,...,27; round keys remain linked to the SAME master. -/
def scheduledFiveKeys (master : V 256) (start : Fin 28) : Fin 5 → Word :=
  fun i => roundKey master ⟨start.val + i.val, by omega⟩

private theorem scheduledFiveKeys_eq (master : V 256) (start : Fin 28) :
    scheduledFiveKeys master start =
      Magma.DiffanFiveRoundCoreDefect.fiveRoundKeys (roundKey master ⟨start.val, by omega⟩)
        (roundKey master ⟨start.val + 1, by omega⟩) (roundKey master ⟨start.val + 2, by omega⟩)
        (roundKey master ⟨start.val + 3, by omega⟩)
        (roundKey master ⟨start.val + 4, by omega⟩) := by
  funext i
  fin_cases i <;> rfl

/-- Key-scheduled impossible differential: for every master key,
    every start of a five-round ordinary-G window, and every a ≠ 0,
    the differential (a,0) → (0,a) has exactly zero witnesses. -/
theorem scheduledFive_diagonal_impossible
    (master : V 256) (start : Fin 28) (a : Word)
    (ha : a ≠ (0#32)) :
    xorDDT_rounds 5 (scheduledFiveKeys master start)
      (a, 0#32) (0#32, a) = 0 := by
  rw [scheduledFiveKeys_eq]
  exact fiveRound_diagonal_impossible
    (roundKey master ⟨start.val, by omega⟩)
    (roundKey master ⟨start.val + 1, by omega⟩)
    (roundKey master ⟨start.val + 2, by omega⟩)
    (roundKey master ⟨start.val + 3, by omega⟩)
    (roundKey master ⟨start.val + 4, by omega⟩)
    a ha

/-- For zero input difference, the local round-function zero-output
    coefficient is positive: a concrete base word supplies a witness. -/
private theorem gDDT_zero_zero_positive (k : Word) :
    0 < xorDDT_g k (0#32) (0#32) := by
  unfold xorDDT_g
  apply Finset.card_pos.mpr
  refine ⟨(0#32), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (g k ((0#32) ^^^ (0#32))) ^^^ (g k (0#32)) = (0#32)
  simp only [BitVec.xor_self]

/-- Exact support classification of the five-round diagonal, at
    ANY fixed five round keys: it is reachable iff a=0. -/
theorem fiveRound_diagonal_support_iff_zero
    (k₀ k₁ k₂ k₃ k₄ a : Word) :
    0 < xorDDT_rounds 5
      (Magma.DiffanFiveRoundCoreDefect.fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, a) ↔ a = (0#32) := by
  constructor
  · intro h
    by_contra ha
    have hz := fiveRound_diagonal_impossible k₀ k₁ k₂ k₃ k₄ a ha
    rw [hz] at h
    omega
  · intro ha
    subst a
    rw [Magma.DiffanFiveRoundCoreDefect.fiveRound_eq_threeCore,
      threeRound_middleDiagonal_factorization]
    exact Nat.mul_pos (gDDT_zero_zero_positive k₁)
      (gDDT_zero_zero_positive k₃)

/-- The same full support classification holds for every five-round
    window of the REAL Magma key schedule. -/
theorem scheduledFive_diagonal_support_iff_zero
    (master : V 256) (start : Fin 28) (a : Word) :
    0 < xorDDT_rounds 5 (scheduledFiveKeys master start)
      (a, 0#32) (0#32, a) ↔ a = (0#32) := by
  rw [scheduledFiveKeys_eq]
  exact fiveRound_diagonal_support_iff_zero
    (roundKey master ⟨start.val, by omega⟩)
    (roundKey master ⟨start.val + 1, by omega⟩)
    (roundKey master ⟨start.val + 2, by omega⟩)
    (roundKey master ⟨start.val + 3, by omega⟩)
    (roundKey master ⟨start.val + 4, by omega⟩)
    a

end Magma.DiffanDiagonalSupportScheduledWindows
