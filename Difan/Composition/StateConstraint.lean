module

import all Init.Data.Range.Basic
public import Difan.Core.DifferentialMap

@[expose] public section

/-!
# Difan.Composition.StateConstraint

Predicates on an actual state *with its difference*. Unlike predicates on a
marginal difference, these can be propagated exactly backward along any
concrete transformation; injectivity is not required.
-/

namespace Difan

/-- A condition on a concrete base state together with its difference. -/
abbrev StateConstraint (X A : Type*) := StateDifference X A → Prop

namespace StateConstraint

/-- Both conditions must hold for the same concrete state/difference pair. -/
def intersect {X A : Type*}
    (P Q : StateConstraint X A) : StateConstraint X A :=
  fun p => P p ∧ Q p

/-- Embed an ordinary base-state condition. -/
def onBase {X A : Type*} (P : X → Prop) : StateConstraint X A :=
  fun p => P p.base

/-- Embed a condition on differences alone; this forgets the base state. -/
def onDelta {X A : Type*} (P : A → Prop) : StateConstraint X A :=
  fun p => P p.delta

/-- Pull an output condition backward through a concrete map. -/
def pullback {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy)
    (Q : StateConstraint Y B) : StateConstraint X A :=
  fun p => Q (f.transport p)

/-- Constraints commute with backward transport and conjunction. -/
theorem pullback_intersect {X Y A B : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    (f : DifferentialMap sx sy)
    (P Q : StateConstraint Y B) :
    pullback f (intersect P Q) =
      intersect (pullback f P) (pullback f Q) := rfl

/-- The backward order is the reverse of the execution order.
    First execute `f`, then `g`: pull back through `g`, then `f`. -/
theorem pullback_comp {X Y Z A B C : Type*}
    {sx : DifferenceSpace X A} {sy : DifferenceSpace Y B}
    {sz : DifferenceSpace Z C}
    (f : DifferentialMap sx sy) (g : DifferentialMap sy sz)
    (Q : StateConstraint Z C) :
    pullback (f.comp g) Q = pullback f (pullback g Q) := by
  funext p
  change Q ((f.comp g).transport p) = Q (g.transport (f.transport p))
  rw [← DifferentialMap.transport_comp f g p]

end StateConstraint

end Difan
