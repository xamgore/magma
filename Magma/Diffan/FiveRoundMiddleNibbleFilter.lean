module

public import Magma.Diffan.FirstActiveNibbleInvariant
import all Init.Data.Range.Basic

set_option maxRecDepth 2048

@[expose] public section

/-!
# A second structural obstruction to five-round Magma differentials

Unlike SAT output, the results here are derived from the actual definitions of
`gDifference` and `xorDDT_rounds`. The remaining index compatibility
condition quantifies over one intermediate 32-bit word, not a round key.
-/

namespace Magma.DiffanFiveRoundMiddleNibbleFilter

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFirstActiveNibbleInvariant

abbrev Word := V 32

private theorem firstActiveNibbleAt_unique
    (d : Word) (i j : Fin 8)
    (hi : FirstActiveNibbleAt d i)
    (hj : FirstActiveNibbleAt d j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hi.2 (hj.1 i hlt)
  · exact hj.2 (hi.1 j hgt)

private theorem firstActiveNibbleAt_exists (d : Word) (hd : d ≠ 0#32) :
    ∃ i : Fin 8, FirstActiveNibbleAt d i := by
  classical
  have hex : ∃ i : Fin 8, wordDigits d i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : wordDigits d = wordDigits (0#32) := by
      funext i
      have hz : wordDigits (0#32) i = 0 := by fin_cases i <;> decide
      exact (h i).trans hz.symm
    exact hd (wordDigitsEquiv.injective hz)
  let s : Finset (Fin 8) := Finset.univ.filter (fun i => wordDigits d i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i : Fin 8 := s.min' hs
  refine ⟨i, ?_, ?_⟩
  · intro u hu
    by_contra hn
    have humem : u ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    have hmin := Finset.min'_le s u humem
    exact (not_lt_of_ge hmin) hu
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2

private theorem gDifference_zero_input (k x : Word) :
    gDifference k x (0#32) = 0#32 := by
  simp [gDifference, Magma.xor, BitVec.xor_zero]

/-- First-active-nibble preservation can also be read backwards from a
    nonzero round-function output difference to its input difference. -/
theorem firstActiveNibble_from_output
    (k d x : Word) (j : Fin 8)
    (ho : FirstActiveNibbleAt ((gDifference k x d).rotateRight 11) j) :
    FirstActiveNibbleAt d j := by
  have hne : d ≠ 0#32 := by
    intro hz
    subst d
    rw [gDifference_zero_input] at ho
    have hzero : (0#32 : Word).rotateRight 11 = 0#32 := by decide
    rw [hzero] at ho
    exact ho.2 (by fin_cases j <;> decide)
  obtain ⟨i, hi⟩ := firstActiveNibbleAt_exists d hne
  have hp := firstActiveNibble_preserved k d x i hi
  have heq : i = j := firstActiveNibbleAt_unique _ i j hp ho
  simpa [heq] using hi

/-- A key-independent incompatibility criterion on two first-active
    nibble indices. It asserts the absence of an intermediate word with
    those two nibble positions before and after the 11-bit rotation. -/
def NoCompatibleMiddleWord (i j : Fin 8) : Prop :=
  ∀ c : Word,
    ¬ (FirstActiveNibbleAt (c.rotateRight 11) i ∧ FirstActiveNibbleAt c j)

/-- The second structural obstruction. It is independent of the five
    round keys, and it reduces an impossible differential to the absence
    of an intermediate 32-bit word with two specified nibble indices. -/
theorem fiveRound_zero_of_no_compatible_middle
    (k₀ k₁ k₂ k₃ k₄ a s : Word) (i j : Fin 8)
    (ha : FirstActiveNibbleAt a i)
    (hm : FirstActiveNibbleAt ((Magma.xor s a).rotateRight 11) j)
    (hbad : NoCompatibleMiddleWord i j) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three]
  classical
  unfold threeRoundCoupledCount
  have hn : ∀ p : FeistelState,
      ¬ threeRoundCoupled k₁ k₂ k₃ (0#32) a s (0#32) p.1 p.2 := by
    rintro ⟨R, Z⟩ hc
    let c : Word := gDifference k₁ R a
    have houter : FirstActiveNibbleAt (c.rotateRight 11) i :=
      firstActiveNibble_preserved k₁ a R i ha
    have hmid : gDifference k₂ Z c = Magma.xor s a := by
      have h := hc.1
      change (gDifference k₂ Z ((gDifference k₁ R a) ^^^ (0#32))) ^^^ a = s at h
      simp only [BitVec.xor_zero] at h
      have hx := congrArg (fun v : Word => v ^^^ a) h
      change gDifference k₂ Z c = s ^^^ a
      simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hx
    have hmiddle : FirstActiveNibbleAt c j := by
      apply firstActiveNibble_from_output k₂ c Z j
      rw [hmid]
      exact hm
    exact (hbad c) ⟨houter, hmiddle⟩
  simp [hn]

end Magma.DiffanFiveRoundMiddleNibbleFilter
