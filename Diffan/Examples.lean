module

public import Diffan.Composition
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Examples — small kernel-checkable mathematical examples

All computations have at most eight input states. No expensive 32-bit scans.
The toy nonlinear map provides a *strict* counterexample to exact support
composition: F ∘ F = identity, but composing supports introduces false paths.
-/

namespace Diffan.Examples

open Diffan

/-- Boolean XOR, as a tiny difference space. -/
def boolSpace : DifferenceSpace Bool Bool where
  shift := Bool.xor
  diff := Bool.xor
  shift_diff := by
    intro x y
    cases x <;> cases y <;> rfl
  diff_shift := by
    intro x a
    cases x <;> cases a <;> rfl

/-- An identity map sends every input difference to the same difference. -/
example : ddt boolSpace boolSpace (fun x : Bool => x) true true = 2 := by
  decide

/-- The other output difference is impossible. -/
example : ddt boolSpace boolSpace (fun x : Bool => x) true false = 0 := by
  decide

/-- Symbolic key restrictions can be combined without enumerating keys. -/
example (k : Nat) :
    KeyConstraint.intersect (fun n : Nat => n % 16 = 7)
      (fun n : Nat => n % 2 = 1) k ↔
    k % 16 = 7 ∧ k % 2 = 1 := by
  rfl

/-- A three-bit toy space. It is NOT an implementation of Magma. -/
abbrev Triple := Bool × (Bool × Bool)

def xor3 (x y : Triple) : Triple :=
  (Bool.xor x.1 y.1, (Bool.xor x.2.1 y.2.1, Bool.xor x.2.2 y.2.2))

def tripleSpace : DifferenceSpace Triple Triple where
  shift := xor3
  diff := xor3
  shift_diff := by decide
  diff_shift := by decide

/-- A small nonlinear involution: F(x,y,z)=(x,y,z XOR (x AND y)). -/
def nonlinearToy (x : Triple) : Triple :=
  (x.1, (x.2.1, Bool.xor x.2.2 (x.1 && x.2.1)))

theorem nonlinearToy_involutive (x : Triple) : nonlinearToy (nonlinearToy x) = x := by
  rcases x with ⟨x, ⟨y, z⟩⟩
  cases x <;> cases y <;> cases z <;> rfl

/-- The input difference toggles the first bit. -/
def a : Triple := (true, (false, false))

/-- The chosen output difference toggles the first and last bits. -/
def c : Triple := (true, (false, true))

/-- Abstract composition of one-step supports admits `a → c`. -/
theorem abstract_path_exists :
    composeSupport
      (support tripleSpace tripleSpace nonlinearToy)
      (support tripleSpace tripleSpace nonlinearToy) a c := by
  refine ⟨c, ?_, ?_⟩
  · refine ⟨(false, (true, false)), ?_⟩
    decide
  · refine ⟨(false, (false, false)), ?_⟩
    decide

/-- But the actual *two-step transformation* is identity and excludes `a → c`. -/
theorem actual_two_step_impossible :
    ¬ support tripleSpace tripleSpace
      (nonlinearToy ∘ nonlinearToy) a c := by
  rintro ⟨x, hx⟩
  have hid :
      derivative tripleSpace tripleSpace
        (nonlinearToy ∘ nonlinearToy) a x = a := by
    simp only [derivative, Function.comp_apply, nonlinearToy_involutive]
    exact tripleSpace.diff_shift x a
  have hac : a = c := hid.symm.trans hx
  exact (by decide : a ≠ c) hac

/-- Therefore the support inclusion can be strict. -/
theorem support_composition_can_be_strict :
    composeSupport
      (support tripleSpace tripleSpace nonlinearToy)
      (support tripleSpace tripleSpace nonlinearToy) a c ∧
    ¬ support tripleSpace tripleSpace
      (nonlinearToy ∘ nonlinearToy) a c :=
  ⟨abstract_path_exists, actual_two_step_impossible⟩

end Diffan.Examples
