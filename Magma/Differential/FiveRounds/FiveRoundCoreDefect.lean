module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.FirstRoundDeletion
public import Magma.Differential.ThreeRounds.ThreeRoundConvolutionDefect

@[expose] public section

/-!
# Five-round boundary reduction and exact core defect

A zero right INPUT difference and a zero left OUTPUT difference remove
both outer ordinary Feistel rounds, leaving a three-round core.

Unlike the four-round case, the three-round core does not automatically
factor into a product. Instead, the already certified three-round coupling
defect gives the EXACT identity

  D5((aL,0),(0,bR)) + defect3((0,aL),(bR,0))
      = ∑ c, D_g[k1](aL,c) * D_g[k2](c,bR XOR aL).

This is a statement about fixed round-key words, not an assumption of
independent subkeys. Repeated words of the Magma master key must still be
identified when instantiating the key schedule.
-/

namespace Magma.DifanFiveRoundCoreDefect

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanThreeRoundConvolutionDefect
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- Five consecutive ordinary Feistel rounds, in execution order. -/
def fiveRoundKeys (k₀ k₁ k₂ k₃ k₄ : Word) : Fin 5 → Word :=
  ![k₀, k₁, k₂, k₃, k₄]

/-- Deleting the two outer entries really leaves k1,k2,k3 in order. -/
private theorem innerKeys (k₀ k₁ k₂ k₃ k₄ : Word) :
    (fun i : Fin 3 => (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) i.castSucc.succ) =
      threeRoundKeys k₁ k₂ k₃ := by
  funext i
  fin_cases i <;> rfl

/-- The full five-round differential is exactly a three-round differential
    on its inner core, for every fixed set of five round keys. -/
theorem fiveRound_eq_threeCore (k₀ k₁ k₂ k₃ k₄ aL bR : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) =
    xorDDT_rounds 3 (threeRoundKeys k₁ k₂ k₃)
      (0#32, aL) (bR, 0#32) := by
  have h := Magma.DifanFirstRoundDeletion.twoSided_boundary_ddt_eq_inner 3
    (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) aL bR
  rw [innerKeys] at h
  exact h

/-- The right-input-zero/left-output-zero slice is independent of both
    outside round keys, when the THREE inner keys are fixed. -/
theorem fiveRound_independent_outer_keys
    (k₀ k₀' k₁ k₂ k₃ k₄ k₄' aL bR : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) =
    xorDDT_rounds 5 (fiveRoundKeys k₀' k₁ k₂ k₃ k₄')
      (aL, 0#32) (0#32, bR) := by
  rw [fiveRound_eq_threeCore, fiveRound_eq_threeCore]

/-- The five-round coefficient plus the EXACT rejected
    trajectory count equals the convolution of two inner round-function
    DDTs.  This strengthens a mere convolution upper bound. -/
theorem fiveRound_add_coreDefect_eq_convolution
    (k₀ k₁ k₂ k₃ k₄ aL bR : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (aL, 0#32) (0#32, bR) +
      couplingDefect k₁ k₂ k₃ (0#32) aL bR (0#32) =
    ∑ c : Word,
      xorDDT_g k₁ aL c * xorDDT_g k₂ c (xor bR aL) := by
  have hcore :=
    actual_add_defect_eq_convolution
      k₁ k₂ k₃ (0#32) aL bR (0#32)
  have hzero (c : Word) : xor c (0#32) = c := by
    change c ^^^ (0#32) = c
    exact BitVec.xor_zero
  calc
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (aL, 0#32) (0#32, bR) +
        couplingDefect k₁ k₂ k₃ (0#32) aL bR (0#32) =
      xorDDT_rounds 3 (threeRoundKeys k₁ k₂ k₃)
        (0#32, aL) (bR, 0#32) +
        couplingDefect k₁ k₂ k₃ (0#32) aL bR (0#32) := by
          rw [fiveRound_eq_threeCore]
    _ = ∑ c : Word,
        xorDDT_g k₁ aL (xor c (0#32)) *
          xorDDT_g k₂ c (xor bR aL) := hcore
    _ = ∑ c : Word,
        xorDDT_g k₁ aL c * xorDDT_g k₂ c (xor bR aL) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hzero c]

/-- The exact convolution is a certified upper bound on the five-round
    coefficient. The missing mass is explicitly `couplingDefect`. -/
theorem fiveRound_le_convolution (k₀ k₁ k₂ k₃ k₄ aL bR : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) ≤
    ∑ c : Word,
      xorDDT_g k₁ aL c * xorDDT_g k₂ c (xor bR aL) := by
  have h := fiveRound_add_coreDefect_eq_convolution
    k₀ k₁ k₂ k₃ k₄ aL bR
  omega

/-- Convolution is exact if and only if the inner three-round coupling
    defect vanishes. This is the precise remaining factorization question. -/
theorem fiveRound_eq_convolution_iff_coreDefect_zero
    (k₀ k₁ k₂ k₃ k₄ aL bR : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) =
      (∑ c : Word,
        xorDDT_g k₁ aL c * xorDDT_g k₂ c (xor bR aL)) ↔
      couplingDefect k₁ k₂ k₃ (0#32) aL bR (0#32) = 0 := by
  have h := fiveRound_add_coreDefect_eq_convolution
    k₀ k₁ k₂ k₃ k₄ aL bR
  omega

/-- If the two-function DDT convolution has no compatible intermediate
    difference, the full five-round coefficient vanishes as well. -/
theorem fiveRound_zero_of_convolution_zero
    (k₀ k₁ k₂ k₃ k₄ aL bR : Word)
    (hzero : (∑ c : Word,
      xorDDT_g k₁ aL c * xorDDT_g k₂ c (xor bR aL)) = 0) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) = 0 := by
  have h := fiveRound_add_coreDefect_eq_convolution
    k₀ k₁ k₂ k₃ k₄ aL bR
  rw [hzero] at h
  omega

/-- A support-only criterion for an impossible five-round differential.
    At each intermediate difference c, at least one inner DDT entry must
    vanish. -/
theorem fiveRound_zero_of_disjoint_inner_support
    (k₀ k₁ k₂ k₃ k₄ aL bR : Word)
    (h : ∀ c : Word,
      xorDDT_g k₁ aL c = 0 ∨
        xorDDT_g k₂ c (xor bR aL) = 0) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (aL, 0#32) (0#32, bR) = 0 := by
  apply fiveRound_zero_of_convolution_zero
  apply Finset.sum_eq_zero
  intro c _
  rcases h c with hc | hc
  · rw [hc, zero_mul]
  · rw [hc, mul_zero]

end Magma.DifanFiveRoundCoreDefect
