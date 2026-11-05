module

import all Init.Data.Range.Basic
public import Diffan.Core.Constraints

@[expose] public section

/-!
# Diffan.ScheduledConstraints — constraints on a common parameter

A deterministic schedule turns a master parameter `m : M` and a position
`i : I` into a local parameter `schedule m i : K`. A constraint on the
local parameter is lifted to a predicate on the **same** master parameter.

This file is cipher-independent. An equality of two scheduled local
parameters allows their constraints to be intersected at a single value.
-/

namespace Diffan.KeyConstraint

/-- Pull a condition on the local parameter at step `i` back to `M`. -/
def atStep {M I K : Type*}
    (schedule : M → I → K) (i : I) (P : KeyConstraint K) :
    KeyConstraint M :=
  KeyConstraint.pullback (fun m => schedule m i) P

/-- Intersection commutes with substitution of a scheduled parameter. -/
theorem atStep_intersect {M I K : Type*}
    (schedule : M → I → K) (i : I)
    (P Q : KeyConstraint K) :
    KeyConstraint.intersect (atStep schedule i P) (atStep schedule i Q) =
      atStep schedule i (KeyConstraint.intersect P Q) := by
  rfl

/-- If the schedule uses the same local parameter at two positions,
    their corresponding lifted conditions coincide. -/
theorem atStep_eq_of_schedule_eq {M I K : Type*}
    (schedule : M → I → K) (i j : I) (P : KeyConstraint K)
    (h : ∀ m, schedule m i = schedule m j) :
    atStep schedule i P = atStep schedule j P := by
  funext m
  exact congrArg P (h m)

/-- Two conditions at repeated positions are conditions on one and the
    same local parameter, not on independently quantified parameters. -/
theorem intersect_atStep_of_schedule_eq {M I K : Type*}
    (schedule : M → I → K) (i j : I)
    (P Q : KeyConstraint K)
    (h : ∀ m, schedule m i = schedule m j) :
    KeyConstraint.intersect (atStep schedule i P) (atStep schedule j Q) =
      atStep schedule i (KeyConstraint.intersect P Q) := by
  rw [← atStep_eq_of_schedule_eq schedule i j Q h]
  exact atStep_intersect schedule i P Q

/-- Incompatible local conditions remain incompatible when the same
    scheduled parameter is reused at two steps. -/
theorem not_intersect_atStep_of_schedule_eq {M I K : Type*}
    (schedule : M → I → K) (i j : I)
    (P Q : KeyConstraint K)
    (h : ∀ m, schedule m i = schedule m j)
    (hdisjoint : ∀ k, ¬ (P k ∧ Q k)) (m : M) :
    ¬ KeyConstraint.intersect (atStep schedule i P)
        (atStep schedule j Q) m := by
  rw [intersect_atStep_of_schedule_eq schedule i j P Q h]
  exact hdisjoint (schedule m i)

end Diffan.KeyConstraint
