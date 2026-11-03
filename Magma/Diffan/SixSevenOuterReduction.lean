module
import all Init.Data.Range.Basic
public import Magma.Diffan.FirstRoundDeletion
public import Magma.Diffan.FiveRoundCoreDefect

@[expose] public section

/-!
# Exact six/seven-round outer DDT reductions

The general fixed-key boundary fiber equivalence for n+2 rounds
specializes to a four-round core after six outer rounds, and a
five-round core after seven. Both equalities hold for arbitrary
round keys, including repeated words from the RFC 8891 schedule.
-/

namespace Magma.DiffanSixSevenOuterReduction

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFirstRoundDeletion
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFourRoundZeroLeftFactorization

private abbrev Word :=
  V 32

def sixRoundKeys (k₀ k₁ k₂ k₃ k₄ k₅ : Word) : Fin 6 → Word :=
  ![k₀, k₁, k₂, k₃, k₄, k₅]

def sevenRoundKeys (k₀ k₁ k₂ k₃ k₄ k₅ k₆ : Word) : Fin 7 → Word :=
  ![k₀, k₁, k₂, k₃, k₄, k₅, k₆]

theorem sixRound_outer_eq_fourCore (k₀ k₁ k₂ k₃ k₄ k₅ a s : Word) :
    xorDDT_rounds 6 (sixRoundKeys k₀ k₁ k₂ k₃ k₄ k₅) (a, 0#32) (0#32, s) =
      xorDDT_rounds 4 (fourRoundKeys k₁ k₂ k₃ k₄) (0#32, a) (s, 0#32) := by
  have hk :
    (fun i : Fin 4 => (sixRoundKeys k₀ k₁ k₂ k₃ k₄ k₅) i.castSucc.succ) =
      fourRoundKeys k₁ k₂ k₃ k₄ := by
    funext i
    fin_cases i <;> rfl
  have h := twoSided_boundary_ddt_eq_inner 4 (sixRoundKeys k₀ k₁ k₂ k₃ k₄ k₅) a s
  rw [hk] at h
  exact h

theorem sevenRound_outer_eq_fiveCore (k₀ k₁ k₂ k₃ k₄ k₅ k₆ a s : Word) :
    xorDDT_rounds 7 (sevenRoundKeys k₀ k₁ k₂ k₃ k₄ k₅ k₆) (a, 0#32) (0#32, s) =
      xorDDT_rounds 5 (fiveRoundKeys k₁ k₂ k₃ k₄ k₅) (0#32, a) (s, 0#32) := by
  have hk :
    (fun i : Fin 5 => (sevenRoundKeys k₀ k₁ k₂ k₃ k₄ k₅ k₆) i.castSucc.succ) =
      fiveRoundKeys k₁ k₂ k₃ k₄ k₅ := by
    funext i
    fin_cases i <;> rfl
  have h := twoSided_boundary_ddt_eq_inner 5 (sevenRoundKeys k₀ k₁ k₂ k₃ k₄ k₅ k₆) a s
  rw [hk] at h
  exact h

theorem sixRound_outer_independent_boundary_keys (k₀ k₀' k₁ k₂ k₃ k₄ k₅ k₅' a s : Word) :
    xorDDT_rounds 6 (sixRoundKeys k₀ k₁ k₂ k₃ k₄ k₅) (a, 0#32) (0#32, s) =
      xorDDT_rounds 6 (sixRoundKeys k₀' k₁ k₂ k₃ k₄ k₅') (a, 0#32) (0#32, s) := by
  rw [sixRound_outer_eq_fourCore, sixRound_outer_eq_fourCore]

theorem sevenRound_outer_independent_boundary_keys (k₀ k₀' k₁ k₂ k₃ k₄ k₅ k₆ k₆' a s : Word) :
    xorDDT_rounds 7 (sevenRoundKeys k₀ k₁ k₂ k₃ k₄ k₅ k₆) (a, 0#32) (0#32, s) =
      xorDDT_rounds 7 (sevenRoundKeys k₀' k₁ k₂ k₃ k₄ k₅ k₆') (a, 0#32) (0#32, s) := by
  rw [sevenRound_outer_eq_fiveCore, sevenRound_outer_eq_fiveCore]

end Magma.DiffanSixSevenOuterReduction
