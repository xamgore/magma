module

public import Mathlib
import all Init.Data.Range.Basic

@[expose] public section

/-!
# States and differences relative to a base point

Applying a difference and recovering it are inverse operations at each
fixed base state. `atBase` packages this coordinate system as an equivalence.
XOR uses the same operation in both directions; other difference conventions
may use distinct operations.
-/

namespace Difan

/-- A space of states `X` with differences in `Δ`.
    The two laws say that fixing an origin identifies states with differences. -/
structure DifferenceSpace (X Δ : Type*) where
  shift : X → Δ → X
  diff : X → X → Δ
  shift_diff : ∀ x y, shift x (diff x y) = y
  diff_shift : ∀ x a, diff x (shift x a) = a

end Difan

namespace Difan.DifferenceSpace

/-- Fixing the base state identifies a difference with its translated state.
This is an equivalence even if the difference type is not a group. -/
def atBase {X Δ : Type*} (s : Difan.DifferenceSpace X Δ)
    (x : X) : Δ ≃ X where
  toFun := s.shift x
  invFun := s.diff x
  left_inv := s.diff_shift x
  right_inv := s.shift_diff x

@[simp]
theorem atBase_apply {X Δ : Type*} (s : Difan.DifferenceSpace X Δ) (x : X) (a : Δ) :
    s.atBase x a = s.shift x a :=
  rfl

@[simp]
theorem atBase_symm_apply {X Δ : Type*} (s : Difan.DifferenceSpace X Δ) (x y : X) :
    (s.atBase x).symm y = s.diff x y :=
  rfl

end Difan.DifferenceSpace
