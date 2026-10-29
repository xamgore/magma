module

public import Mathlib
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Basic — difference spaces and transitions

A difference space provides two mutually inverse operations for each fixed origin:
`shift x a` applies a difference, while `diff x y` extracts it.
For XOR these operations coincide; in general they need not.
-/

namespace Diffan

/-- A space of states `X` with differences in `Δ`.
    The two laws say that fixing an origin identifies states with differences. -/
structure DifferenceSpace (X Δ : Type*) where
  shift : X → Δ → X
  diff : X → X → Δ
  shift_diff : ∀ x y, shift x (diff x y) = y
  diff_shift : ∀ x a, diff x (shift x a) = a

/-- A request for the transition from input difference `a` to output difference `b`. -/
structure Transition (A B : Type*) where
  input : A
  output : B

/-- A transition selected by predicates on its input and output differences.
    Restriction changes the *query domain*, not the underlying DDT. -/
abbrev RestrictedTransition {A B : Type*}
    (inputClass : A → Prop) (outputClass : B → Prop) :=
  {t : Transition A B // inputClass t.input ∧ outputClass t.output}

/-- Output difference of `f`, for an input with base point `x` and difference `a`. -/
def derivative {X Y A B : Type*}
    (sx : DifferenceSpace X A)
    (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (x : X) : B :=
  sy.diff (f x) (f (sx.shift x a))

/-- An identity transformation preserves the input difference. -/
theorem derivative_id {X A : Type*}
    (s : DifferenceSpace X A) (a : A) (x : X) :
    derivative s s (fun y => y) a x = a := by
  exact s.diff_shift x a

/-- The derivative chain rule at a *specific intermediate state*.
    The base point `f x` cannot generally be discarded. -/
theorem derivative_comp {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A)
    (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (a : A) (x : X) :
    derivative sx sz (g ∘ f) a x = derivative sy sz g (derivative sx sy f a x) (f x) := by
  unfold derivative
  simp only [Function.comp_apply]
  rw [sy.shift_diff]

end Diffan
