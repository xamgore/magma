module

public import Diffan.GeneralLaws
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.JointState — exact paired-state semantics

DDT projects away the concrete base state. `pairedBase` retains both
members of a differential pair, so pair transport always composes
exactly, with no Markov or independence assumptions.
-/

namespace Diffan

/-- The concrete state pair associated with base point `x` and
    input difference `a`. -/
def pairedBase {X A : Type*}
    (sx : DifferenceSpace X A) (a : A) (x : X) : X × X :=
  (x, sx.shift x a)

/-- Transport of a concrete pair agrees exactly with the derivative
    together with the *actual* intermediate base state. -/
theorem pairMap_pairedBase {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (x : X) :
    pairMap f (pairedBase sx a x) =
      pairedBase sy (derivative sx sy f a x) (f x) := by
  apply Prod.ext
  · rfl
  · exact (sy.shift_diff (f x) (f (sx.shift x a))).symm

/-- Concrete trajectories always compose exactly on pairs.
    Contrast with the mere inclusion for support relations. -/
theorem concrete_two_steps {X Y Z : Type*}
    (f : X → Y) (g : Y → Z) (xy : X × X) :
    pairMap (g ∘ f) xy = pairMap g (pairMap f xy) := by
  rfl

end Diffan
