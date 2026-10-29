module

public import Diffan.Basic
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Coordinates relative to a base state

For every fixed base state, applying a difference and recovering it are
inverse maps. The two laws of `DifferenceSpace` give this equivalence
without requiring group operations on the difference type.
-/

namespace Diffan.DifferenceSpace

/-- Fixing the base state identifies a difference with its translated state.
This is an equivalence even if the difference type is not a group. -/
def atBase {X Δ : Type*} (s : Diffan.DifferenceSpace X Δ)
    (x : X) : Δ ≃ X where
  toFun := s.shift x
  invFun := s.diff x
  left_inv := s.diff_shift x
  right_inv := s.shift_diff x

@[simp]
theorem atBase_apply {X Δ : Type*} (s : Diffan.DifferenceSpace X Δ) (x : X) (a : Δ) :
    s.atBase x a = s.shift x a :=
  rfl

@[simp]
theorem atBase_symm_apply {X Δ : Type*} (s : Diffan.DifferenceSpace X Δ) (x y : X) :
    (s.atBase x).symm y = s.diff x y :=
  rfl

end Diffan.DifferenceSpace
