module

public import Diffan.GeneralLaws
public import Diffan.StateDifference
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Concrete pairs and state/difference coordinates

A base state and its difference determine both members of an ordered
pair. Transporting that pair applies the same function to both states;
the inverse laws of the difference space identify the result with
transport in state/difference coordinates.
-/

namespace Diffan

/-- The concrete pair encoded by a base point and input difference.
Both states are fixed once the base point and difference are chosen. -/
def pairedBase {X A : Type*}
    (sx : DifferenceSpace X A) (a : A) (x : X) : X × X :=
  (StateDifference.mk x a).toPair sx

/-- Conversion lemmas for `StateDifference` also apply to paired-state
    calculations through this coordinate identity. -/
theorem pairedBase_eq_toPair {X A : Type*}
    (sx : DifferenceSpace X A) (a : A) (x : X) :
    pairedBase sx a x = (StateDifference.mk x a).toPair sx := rfl

/-- Transport of a concrete state pair agrees with difference transport. -/
theorem pairMap_pairedBase {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (a : A) (x : X) :
    pairMap f (pairedBase sx a x) =
      pairedBase sy (derivative sx sy f a x) (f x) := by
  apply Prod.ext
  · rfl
  · exact (sy.shift_diff (f x) (f (sx.shift x a))).symm

/-- Concrete trajectories compose exactly on pairs of states. -/
theorem concrete_two_steps {X Y Z : Type*}
    (f : X → Y) (g : Y → Z) (xy : X × X) :
    pairMap (g ∘ f) xy = pairMap g (pairMap f xy) := rfl

end Diffan
