module
import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.OneHotKeyFreeCarryBridge

@[expose] public section

/-!
# Key-free Boolean carry feasibility

Each nibble chooses its own local key and base digit. Thus the
reachability test overapproximates all real Magma round differences.
A negative result is a sound certificate for universal impossibility.
-/

namespace Magma.DifanKeyFreeCarryAutomaton

open Magma
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanOneHotKeyFreeCarryBridge
open Magma.DifanFiveRoundUniversalSupport

private abbrev Word :=
  V 32

def keyFreeStep (i : Fin 8) (d out : Fin 16) (s t : CarryState) : Bool :=
  decide (∃ k x : Fin 16, sboxCarryStep i k d x s = (out, t))

def keyFreeReach (d out : Fin 8 → Fin 16) : Nat → CarryState → Bool
  | 0, s => decide (s = ((0, 0) : CarryState))
  | n + 1, t =>
    if hn : n < 8 then
      decide
        (∃ s : CarryState,
          keyFreeReach d out n s = true ∧ keyFreeStep ⟨n, hn⟩ (d ⟨n, hn⟩) (out ⟨n, hn⟩) s t = true)
    else false

def keyFreePossible (d out : Word) : Bool :=
  decide
    (∃ t : CarryState, keyFreeReach (wordDigits d) (wordDigits (out.rotateRight 11)) 8 t = true)

/-- A witnessed local path remains reachable in the Boolean automaton. -/
theorem keyFreePossible_of_localPath
    (d out : Word) (h : keyFreeLocalPath d out) :
    keyFreePossible d out = true := by
  obtain ⟨states, hinitial, hstep⟩ := h
  let dd := wordDigits d
  let oo := wordDigits (out.rotateRight 11)
  have hreach : ∀ n : Nat, (hn : n ≤ 8) →
      keyFreeReach dd oo n (states (⟨n, by omega⟩ : Fin 9)) = true := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [keyFreeReach, hinitial]
    | succ n ih =>
        intro hn
        have hn8 : n < 8 := by omega
        have hprev := ih (by omega)
        obtain ⟨k, x, hs⟩ := hstep (⟨n, hn8⟩ : Fin 8)
        have hlocal :
            keyFreeStep (⟨n, hn8⟩ : Fin 8)
              (dd ⟨n, hn8⟩) (oo ⟨n, hn8⟩)
              (states (⟨n, by omega⟩ : Fin 9))
              (states (⟨n + 1, by omega⟩ : Fin 9)) = true := by
          apply (decide_eq_true_eq).mpr
          refine ⟨k, x, ?_⟩
          have hcast : ((⟨n, hn8⟩ : Fin 8).castSucc : Fin 9) =
              (⟨n, by omega⟩ : Fin 9) := by
            apply Fin.ext
            rfl
          have hsucc : ((⟨n, hn8⟩ : Fin 8).succ : Fin 9) =
              (⟨n + 1, by omega⟩ : Fin 9) := by
            apply Fin.ext
            rfl
          rw [hcast, hsucc] at hs
          simpa only [dd, oo] using hs
        change (if h : n < 8 then
          decide (∃ s : CarryState,
            keyFreeReach dd oo n s = true ∧
            keyFreeStep ⟨n, h⟩ (dd ⟨n, h⟩)
              (oo ⟨n, h⟩) s
              (states (⟨n + 1, by omega⟩ : Fin 9)) = true)
          else false) = true
        rw [dite_eq_left hn8]
        exact (decide_eq_true_eq).mpr
          ⟨states (⟨n, by omega⟩ : Fin 9), hprev, hlocal⟩
  apply (decide_eq_true_eq).mpr
  exact ⟨states (8 : Fin 9), hreach 8 (by omega)⟩

theorem keyFreePossible_of_anyKeyGSupport (d out : Word) (h : anyKeyGSupport d out) :
    keyFreePossible d out = true :=
  keyFreePossible_of_localPath d out
    (keyFreeCarrySupport_implies_localPath d out
      (anyKeyGSupport_implies_keyFreeCarrySupport d out h))

/-- A failed Boolean triple-support test excludes all five-round paths. -/
theorem fiveRound_zero_of_boolean_keyFree_conflict
    (k₀ k₁ k₂ k₃ k₄ a s : Word)
    (hno : ∀ c : Word,
      ¬ (keyFreePossible a c = true ∧
         keyFreePossible c (xor s a) = true ∧
         keyFreePossible s c = true)) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0 := by
  apply fiveRound_zero_of_no_anyKey_joint_support
  intro c h
  exact hno c
    ⟨keyFreePossible_of_anyKeyGSupport a c h.1,
     keyFreePossible_of_anyKeyGSupport c (xor s a) h.2.1,
     keyFreePossible_of_anyKeyGSupport s c h.2.2⟩

end Magma.DifanKeyFreeCarryAutomaton
