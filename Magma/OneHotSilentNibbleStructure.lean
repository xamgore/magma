module

public import Magma.OneHotKeyClasses
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Silent and active nibble structure of the original carry automaton

Equal incoming carries and zero input difference give zero output difference
and equal outgoing carries. Conversely, zero input and output differences
force equal incoming carries by injectivity of the RFC S-box. With equal
incoming carries, a nonzero input nibble difference forces nonzero output.

An arbitrary suffix of inactive nibbles preserves diagonal carry states.
The local one-bit predicate is also identified with the original nibble-five
transition relation with equal incoming and outgoing carries. These facts
hold universally for the relevant key digits, carries, and S-box indices.

Factoring the full eight-step path into its prefix, active nibble, and suffix
remains necessary to establish `OneHotClassInvariant`.
-/

open Magma.CarryAutomaton Magma.OneHotKeyClasses

namespace Magma.OneHotSilentNibbleStructure

/-! Small universal 4-bit XOR facts. Each case split uses only 16 values. -/

private theorem xorDigit_zero_right (x : Fin 16) : xorDigit x 0 = x := by fin_cases x <;> decide

private theorem xorDigit_self_zero (x : Fin 16) : xorDigit x x = 0 := by fin_cases x <;> decide

private theorem xorDigit_eq_zero_iff (a b : Fin 16) : xorDigit a b = 0 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem xorDigit_eq_left_iff (a b : Fin 16) : xorDigit a b = a ↔ b = 0 := by
  fin_cases a <;> fin_cases b <;> decide

/-! Adding a fixed key and carry permutes the 16 possible input nibbles.
    Changing a carry by one also changes the resulting nibble. -/

private theorem outputDigit_injective_input (k : Fin 16) (c : Fin 2) :
    Function.Injective (fun x : Fin 16 => outputDigit x k c) := by
  intro x y h
  have hv : (x.val + k.val + c.val) % 16 = (y.val + k.val + c.val) % 16 := by
    exact congrArg Fin.val h
  have hx := x.isLt
  have hy := y.isLt
  have hk := k.isLt
  have hc := c.isLt
  apply Fin.ext
  omega

private theorem outputDigit_injective_carry (x k : Fin 16) :
    Function.Injective (fun c : Fin 2 => outputDigit x k c) := by
  intro c d h
  have hv : (x.val + k.val + c.val) % 16 = (x.val + k.val + d.val) % 16 := congrArg Fin.val h
  have hx := x.isLt
  have hk := k.isLt
  have hc := c.isLt
  have hd := d.isLt
  apply Fin.ext
  omega

/-! ### Silent (inactive) S-boxes -/

/-- If the input difference vanishes and the incoming carry bits coincide,
    the output difference also vanishes and the outgoing carries coincide.
    This is independent of the value of the key nibble and the S-box. -/
theorem silent_sbox_step_diagonal
    (i : Fin 8) (k x : Fin 16) (c : Fin 2) :
    sboxCarryStep i k 0 x (c, c) =
      (0, (nextCarry x k c, nextCarry x k c)) := by
  simp only [sboxCarryStep, xorDigit_zero_right, xorDigit_self_zero]

/-- Conversely, when the input difference is zero, a zero output
    difference forces equal incoming carries. This uses the fact that
    each RFC S-box is a permutation and not merely an arbitrary map. -/
theorem silent_sbox_zero_forces_diagonal
    (i : Fin 8) (k x : Fin 16) (c₀ c₁ : Fin 2)
    (h : (sboxCarryStep i k 0 x (c₀, c₁)).1 = 0) :
    c₀ = c₁ := by
  have h' :
      xorDigit
        (π i (BitVec.ofNat 4 (outputDigit x k c₁).val)).toFin
        (π i (BitVec.ofNat 4 (outputDigit x k c₀).val)).toFin = 0 := by
    simpa only [sboxCarryStep, xorDigit_zero_right] using h
  have hπ :
      π i (BitVec.ofNat 4 (outputDigit x k c₁).val) =
        π i (BitVec.ofNat 4 (outputDigit x k c₀).val) :=
    BitVec.eq_of_toFin_eq ((xorDigit_eq_zero_iff _ _).mp h')
  have hin := (π_is_bijective i).injective hπ
  have hout : outputDigit x k c₁ = outputDigit x k c₀ := by
    have ht := congrArg BitVec.toFin hin
    simpa using ht
  exact (outputDigit_injective_carry x k hout).symm

/-! ### The first changed nibble -/

/-- A nonzero input difference in the first changed nibble CANNOT
    produce a zero output difference if the incoming carries agree.
    This is the basis for excluding all one-hot positions outside
    the active output nibble 5. -/
theorem active_sbox_step_nonzero
    (i : Fin 8) (k d x : Fin 16) (c : Fin 2)
    (hd : d ≠ 0) :
    (sboxCarryStep i k d x (c, c)).1 ≠ 0 := by
  intro hzero
  have h' :
      xorDigit
        (π i (BitVec.ofNat 4
          (outputDigit (xorDigit x d) k c).val)).toFin
        (π i (BitVec.ofNat 4 (outputDigit x k c).val)).toFin = 0 := by
    simpa only [sboxCarryStep] using hzero
  have hπ :
      π i (BitVec.ofNat 4 (outputDigit (xorDigit x d) k c).val) =
        π i (BitVec.ofNat 4 (outputDigit x k c).val) :=
    BitVec.eq_of_toFin_eq ((xorDigit_eq_zero_iff _ _).mp h')
  have hin := (π_is_bijective i).injective hπ
  have hout :
      outputDigit (xorDigit x d) k c = outputDigit x k c := by
    have ht := congrArg BitVec.toFin hin
    simpa using ht
  have heq : xorDigit x d = x :=
    outputDigit_injective_input k c hout
  exact hd ((xorDigit_eq_left_iff x d).mp heq)

/-! ### Arbitrarily many trailing inactive nibbles -/

/-- A list of (S-box index, key digit, input digit) steps on which
    the INPUT DIFFERENCE is identically zero. The output condition is
    checked against zero at each step, just as in carryTrace. -/
def silentRun :
    List (Fin 8 × Fin 16 × Fin 16) → CarryState → CarryState × Bool
  | [], s => (s, true)
  | (i, k, x) :: rest, s =>
      let step := sboxCarryStep i k 0 x s
      let tail := silentRun rest step.2
      (tail.1, decide (step.1 = 0) && tail.2)

/-- No upper S-box can block an already synchronized pair of carry
    chains when all subsequent input XOR differences are zero.
    The upper digits, S-box indices and key digits are completely arbitrary. -/
theorem silentRun_diagonal (steps : List (Fin 8 × Fin 16 × Fin 16))
    (c : Fin 2) :
    ∃ c' : Fin 2, silentRun steps (c, c) = ((c', c'), true) := by
  induction steps generalizing c with
  | nil =>
      exact ⟨c, rfl⟩
  | cons head rest ih =>
      rcases head with ⟨i, k, x⟩
      obtain ⟨c', hc'⟩ := ih (nextCarry x k c)
      refine ⟨c', ?_⟩
      simp [silentRun, silent_sbox_step_diagonal, hc']

/-! ### The active digit is exactly the original local model -/

/-- The verified 32-class local predicate is exactly existence of an
    ORIGINAL S-box/carry transition at nibble 5, with equal incoming
    and outgoing carries. The proof is entirely four-bit arithmetic. -/
theorem localOneHotStepPossible_iff_original_step
    (q : Fin 16) (c : Fin 2) (r : Fin 4) :
    localOneHotStepPossible q c r = true ↔
      ∃ x : Fin 16, ∃ t : Fin 2,
        sboxCarryStep (5 : Fin 8) q (Fin.ofNat 16 (2 ^ r.val))
          x (c, c) = ((2 : Fin 16), (t, t)) := by
  fin_cases q <;> fin_cases c <;> fin_cases r <;> decide

end Magma.OneHotSilentNibbleStructure
