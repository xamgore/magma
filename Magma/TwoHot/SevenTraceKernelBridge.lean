module

public import Magma.TwoHot.UniformTwoDigitKernel
public import Magma.OneHot.TraceSplit5
public import Magma.OneHot.PrefixArithmeticBridge
public import Magma.OneHot.BoundaryReduction
import Mathlib.Tactic.Tauto
import all Init.Data.Range.Basic

@[expose] public section

/-!
Two-hot input XOR difference, output difference 1:
A POINTWISE bridge between the genuine eight-digit carry trace and
`twoDigitSuccess` for the seven classified, strictly ordered pairs.

There is no 32-bit key/input enumeration. Proof proceeds by the exact
5+1+1+1 decomposition of `carryTrace` and the theorems about silent
suffixes. The two cases are (23,24), and the six same-nibble pairs.

This file intentionally stops at an exact SUM over the eight nibble
assignments. In a subsequent small arithmetic bridge, that sum is
rewritten as `uniformSevenCount` using a prefix split and its known
carry-zero/one cardinalities. This separation avoids mixing trace
semantics with the counting algebra.

-/

namespace Magma.TwoHotSevenTraceKernelBridge

open Magma
open Magma.CarryAutomaton
open Magma.OneHotTraceSplit5
open Magma.OneHotPrefixArithmeticBridge
open Magma.OneHotBoundaryReduction
open Magma.OneHotSilentNibbleStructure
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotUniformTwoDigitKernel

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

private abbrev Digit :=
  Fin 16

private abbrev Digits :=
  Fin 8 → Digit

private abbrev State :=
  Fin 2 × Fin 2

private def target : Word :=
  0x00200000#32

private def diff (p : PairBits) : Word :=
  twoHot p.1 p.2

/-- A restatement of the ORIGINAL deterministic carry step, with a
    public name so it can be manipulated independently of private
    implementation details in TraceSplit5. -/
private def oneStep (key delta out input : Digits)
    (acc : State × Bool) (i : Fin 8) : State × Bool :=
  let st := sboxCarryStep i (key i) (delta i) (input i) acc.1
  (st.2, acc.2 && decide (st.1 = out i))

private theorem seven_cases (p : PairBits) (hp : p ∈ sevenPairs) :
    p = (20, 21) ∨
      p = (20, 22) ∨ p = (20, 23) ∨ p = (21, 22) ∨ p = (21, 23) ∨ p = (22, 23) ∨ p = (23, 24) := by
  simpa [sevenPairs] using hp

private theorem target_digits (i : Fin 8) : wordDigits target i = if i = 5 then 2 else 0 := by
  fin_cases i <;> decide

private theorem difference_lower5 (p : PairBits) (hp : p ∈ sevenPairs) (i : Fin 5) :
    wordDigits (diff p) (i.castLE (by decide : 5 ≤ 8)) = 0 := by
  rcases seven_cases p hp with h | h | h | h | h | h | h <;> subst p <;> fin_cases i <;> decide

private theorem difference_digit6 (p : PairBits) (hp : p ∈ sevenPairs) :
    wordDigits (diff p) 6 = if p = crossPair then 1 else 0 := by
  rcases seven_cases p hp with h | h | h | h | h | h | h <;> subst p <;> decide

private theorem difference_digit7 (p : PairBits) (hp : p ∈ sevenPairs) :
    wordDigits (diff p) 7 = 0 := by
  rcases seven_cases p hp with h | h | h | h | h | h | h <;> subst p <;> decide

/-- The first five trace steps always accept and yield a synchronized
    carry. Their state is exactly the ordinary five-digit `lowCarry5`. -/
private theorem seven_prefix5 (key input : Digits) (p : PairBits)
    (hp : p ∈ sevenPairs) :
    tracePrefix5 key (wordDigits (diff p)) (wordDigits target) input =
      ((lowCarry5 key input, lowCarry5 key input), true) := by
  have hsame :
      tracePrefix5 key (wordDigits (diff p)) (wordDigits target) input =
        tracePrefix5 key (oneHotDiffDigits 0) oneHotTargetDigits input := by
    rcases seven_cases p hp with h | h | h | h | h | h | h <;>
      subst p <;> rfl
  rw [hsame]
  exact tracePrefix5_eq_lowCarry5 key input 0

private theorem split_after_five (key delta out input : Digits) :
    carryTrace key delta out input =
      oneStep key delta out input
        (oneStep key delta out input
          (oneStep key delta out input (tracePrefix5 key delta out input) 5) 6)
        7 := by
  exact carryTrace_split_after_five key delta out input

/-- The final zero-difference digit accepts exactly synchronized
    incoming carries; its outgoing carry is discarded. -/
private theorem final_silent_iff (key input : Digits) (s : State) :
    (oneStep key (fun _ => 0) (fun _ => 0) input (s, true) 7).2 = true ↔
      s.1 = s.2 := by
  change decide ((sboxCarryStep 7 (key 7) 0 (input 7) s).1 = 0) = true ↔
    s.1 = s.2
  simp only [decide_eq_true_eq]
  constructor
  · rcases s with ⟨c₀,c₁⟩
    exact silent_sbox_zero_forces_diagonal 7 (key 7) (input 7) c₀ c₁
  · rcases s with ⟨c₀,c₁⟩
    intro h
    change c₀ = c₁ at h
    subst c₁
    have hh := silent_sbox_step_diagonal 7 (key 7) (input 7) c₀
    exact congrArg Prod.fst hh

/-- A pair of silent digits accepts exactly equal incoming carries. -/
private theorem final_two_silent_iff (key input : Digits) (s : State) :
    (oneStep key (fun _ => 0) (fun _ => 0) input
      (oneStep key (fun _ => 0) (fun _ => 0) input (s,true) 6) 7).2 = true ↔
      s.1 = s.2 := by
  have h := nonempty_silent_suffix_iff_diagonal
    (6 : Fin 8) (key 6) (input 6)
    [(7, key 7, input 7)] s
  simpa only [silentRun, oneStep, Bool.true_and, Bool.and_true, Bool.and_assoc] using h

/-- The semantic reduction needed by all seven quantitative formulas:
    the complete deterministic automaton accepts exactly when the two
    locally active digits satisfy the uniform kernel, starting at the
    real carry generated by the five lower input digits.

    The last digit is genuinely free; no final carry restriction is made.
-/
theorem seven_trace_iff_twoDigitSuccess
    (k : Word) (p : PairBits) (hp : p ∈ sevenPairs) (input : Digits) :
    (carryTrace (wordDigits k) (wordDigits (diff p))
      (wordDigits target) input).2 = true ↔
    twoDigitSuccess k p (lowCarry5 (wordDigits k) input)
      (input 5) (input 6) := by
  let key := wordDigits k
  let delta := wordDigits (diff p)
  let out := wordDigits target
  let c := lowCarry5 key input
  let st5 := sboxCarryStep 5 (key 5) (delta 5) (input 5) (c,c)
  have hsplit := split_after_five key delta out input
  rw [seven_prefix5 key input p hp] at hsplit
  have ht5 : out 5 = 2 := target_digits 5
  have ht6 : out 6 = 0 := target_digits 6
  have ht7 : out 7 = 0 := target_digits 7
  have hd7 : delta 7 = 0 := difference_digit7 p hp
  by_cases hcross : p = crossPair
  · subst p
    simp only [twoDigitSuccess]
    have hd6 : delta 6 = 1 := by
      simpa [delta, diff, crossPair] using
        (difference_digit6 crossPair (by decide : crossPair ∈ sevenPairs))
    let st6 := sboxCarryStep 6 (key 6) 1 (input 6) st5.2
    rw [hsplit]
    change
      (oneStep key delta out input
        (oneStep key delta out input
          (st5.2, decide (st5.1 = 2)) 6) 7).2 = true ↔
        (st5.1 = 2 ∧ st6.1 = 0 ∧ st6.2.1 = st6.2.2)
    have hbool :
        (oneStep key delta out input
          (oneStep key delta out input
            (st5.2, decide (st5.1 = 2)) 6) 7).2 =
        ((decide (st5.1 = 2) && decide (st6.1 = 0)) &&
          (oneStep key (fun _ => 0) (fun _ => 0) input
            (st6.2, true) 7).2) := by
      simp only [oneStep, hd6, hd7, ht6, ht7, st6,
        Bool.true_and, Bool.and_assoc]
    rw [hbool, Bool.and_eq_true_iff, Bool.and_eq_true_iff]
    simp only [decide_eq_true_eq]
    rw [final_silent_iff]
    tauto
  · simp only [twoDigitSuccess, ite_eq_right hcross]
    have hd6 : delta 6 = 0 := by
      simpa only [delta] using
        (by simpa [hcross] using difference_digit6 p hp)
    rw [hsplit]
    change
      (oneStep key delta out input
        (oneStep key delta out input
          (st5.2, decide (st5.1 = 2)) 6) 7).2 = true ↔
        (st5.1 = 2 ∧ st5.2.1 = st5.2.2)
    have hbool :
        (oneStep key delta out input
          (oneStep key delta out input
            (st5.2, decide (st5.1 = 2)) 6) 7).2 =
        (decide (st5.1 = 2) &&
          (oneStep key (fun _ => 0) (fun _ => 0) input
            (oneStep key (fun _ => 0) (fun _ => 0) input
              (st5.2,true) 6) 7).2) := by
      simp only [oneStep, hd6, hd7, ht6, ht7,
        Bool.true_and, Bool.and_assoc]
    rw [hbool, Bool.and_eq_true_iff]
    simp only [decide_eq_true_eq]
    rw [final_two_silent_iff]

/-- The true DP count is an eight-digit sum of the UNIFORM local
    kernel. This is unconditional and already eliminates all original
    full-trace bookkeeping from the numeric expression. -/
theorem carryDP_eq_twoDigit_kernel_sum
    (k : Word) (p : PairBits) (hp : p ∈ sevenPairs) :
    carryDPCount (wordDigits k) (wordDigits (diff p))
        (wordDigits target) =
      ∑ input : Digits,
        if twoDigitSuccess k p (lowCarry5 (wordDigits k) input)
          (input 5) (input 6) then (1 : Nat) else 0 := by
  rw [← carryWordCount_eq_carryDPCount]
  rw [carryWordCount_eq_digitAssignments, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro input _
  exact if_congr (seven_trace_iff_twoDigitSuccess k p hp input) rfl rfl

end Magma.TwoHotSevenTraceKernelBridge
