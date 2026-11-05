module

import all Init.Data.Range.Basic
public import Difan.Composition.StateConstraint
public import Difan.Core.Constraints

@[expose] public section

/-!
# Difan.Parameters.KeyStateConstraint

Joint predicates on one parameter (e.g., a master key) and an actual
state/difference pair. Neither a key constraint nor a difference-only
constraint is enough to describe exact bidirectional trajectory matching.
-/

namespace Difan

/-- A joint condition on a parameter and a concrete state/difference pair. -/
abbrev KeyStateConstraint (K X A : Type*) :=
  K → StateDifference X A → Prop

namespace KeyStateConstraint

/-- Conjoin conditions without choosing independent parameters or states. -/
def intersect {K X A : Type*}
    (P Q : KeyStateConstraint K X A) : KeyStateConstraint K X A :=
  fun k p => P k p ∧ Q k p

/-- Lift a pure key restriction into the joint space. -/
def fromKey {K X A : Type*}
    (P : KeyConstraint K) : KeyStateConstraint K X A :=
  fun k _ => P k

/-- Lift a pure state/difference restriction into the joint space. -/
def fromState {K X A : Type*}
    (P : StateConstraint X A) : KeyStateConstraint K X A :=
  fun _ p => P p

/-- Convert a local-parameter restriction into a master-parameter one. -/
def pullbackKey {M K X A : Type*}
    (schedule : M → K) (P : KeyStateConstraint K X A) :
    KeyStateConstraint M X A :=
  fun master p => P (schedule master) p

/-- Pull joint constraints backward through parameter-dependent maps. -/
def pullbackStep {K X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (family : K → DifferentialMap sx sy)
    (Q : KeyStateConstraint K Y B) : KeyStateConstraint K X A :=
  fun k p => Q k ((family k).transport p)

/-- Pullback preserves intersection; the same key is used on both sides. -/
theorem pullbackKey_intersect {M K X A : Type*}
    (schedule : M → K) (P Q : KeyStateConstraint K X A) :
    pullbackKey schedule (intersect P Q) =
      intersect (pullbackKey schedule P) (pullbackKey schedule Q) := rfl

/-- Backward step transport also preserves joint intersection. -/
theorem pullbackStep_intersect {K X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (family : K → DifferentialMap sx sy)
    (P Q : KeyStateConstraint K Y B) :
    pullbackStep family (intersect P Q) =
      intersect (pullbackStep family P) (pullbackStep family Q) := rfl

end KeyStateConstraint

end Difan
