module

import all Init.Data.Range.Basic
public import Diffan.Composition.Meet
public import Diffan.Core.StateDifference

@[expose] public section

/-!
# Midpoint observations versus exact meets

A projected midpoint (a difference, a carry label, or selected bits) can
reject impossible exact meets. Equality of projected values cannot by itself
certify that two trajectories have a common concrete intermediate state.

The full midpoint `StateDifference X A` contains both the base state and the
difference. Equality of those two fields is sufficient for an exact meet.
All results below are independent of any particular cipher or key schedule.
-/

namespace Diffan.MiddleObservation

/-- Both sides reach equal observations of their midpoint. The right
    endpoint is reconstructed backward through the right equivalence. -/
def observedMeets {I O X A L : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (observe : StateDifference X A → L)
    (initial : I) (final : O) : Prop :=
  observe (left initial) = observe (right.symm final)

/-- Every real meet survives every observation, even one losing information. -/
theorem exact_implies_observed {I O X A L : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (observe : StateDifference X A → L)
    (initial : I) (final : O)
    (h : Diffan.Meet.meets left right initial final) :
    observedMeets left right observe initial final := by
  unfold Diffan.Meet.meets at h
  exact congrArg observe h

/-- A mismatch of any projected midpoint rigorously rejects the full meet. -/
theorem no_exact_of_observation_mismatch {I O X A L : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (observe : StateDifference X A → L)
    (initial : I) (final : O)
    (h : ¬ observedMeets left right observe initial final) :
    ¬ Diffan.Meet.meets left right initial final := by
  intro hexact
  exact h (exact_implies_observed left right observe initial final hexact)

/-- Equality of the actual base state at the midpoint. -/
def baseMeets {I O X A : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (initial : I) (final : O) : Prop :=
  observedMeets left right (fun p => p.base) initial final

/-- Equality of the midpoint difference, which may admit false positives. -/
def differenceMeets {I O X A : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (initial : I) (final : O) : Prop :=
  observedMeets left right (fun p => p.delta) initial final

/-- The complete test: base and difference agree at the same midpoint. -/
theorem exact_iff_base_and_difference {I O X A : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (initial : I) (final : O) :
    Diffan.Meet.meets left right initial final ↔
      baseMeets left right initial final ∧
        differenceMeets left right initial final := by
  constructor
  · intro h
    exact ⟨exact_implies_observed left right (fun p => p.base)
        initial final h,
      exact_implies_observed left right (fun p => p.delta)
        initial final h⟩
  · rintro ⟨hb, hd⟩
    change (left initial).base = (right.symm final).base at hb
    change (left initial).delta = (right.symm final).delta at hd
    unfold Diffan.Meet.meets
    cases hleft : left initial with
    | mk lb ld =>
      cases hright : right.symm final with
      | mk rb rd =>
        have hbase : lb = rb := by simpa [hleft, hright] using hb
        have hdelta : ld = rd := by simpa [hleft, hright] using hd
        cases hbase
        cases hdelta
        rfl

/-- Failure of either of the two complete fields forbids a real meet. -/
theorem no_exact_of_base_mismatch {I O X A : Type*}
    (left : I ≃ StateDifference X A)
    (right : StateDifference X A ≃ O)
    (initial : I) (final : O)
    (h : ¬ baseMeets left right initial final) :
    ¬ Diffan.Meet.meets left right initial final :=
  no_exact_of_observation_mismatch left right (fun p => p.base)
    initial final h

/-- Even the identity execution has false midpoint matches if only
    differences are compared and the base states differ. -/
theorem difference_agreement_not_sufficient :
    ∃ p q : StateDifference Bool Bool,
      differenceMeets (Equiv.refl _) (Equiv.refl _) p q ∧
        ¬ Diffan.Meet.meets (Equiv.refl _) (Equiv.refl _) p q := by
  refine ⟨⟨false, false⟩, ⟨true, false⟩, rfl, ?_⟩
  intro h
  change (⟨false, false⟩ : StateDifference Bool Bool) =
    (⟨true, false⟩ : StateDifference Bool Bool) at h
  have hb : false = true :=
    congrArg (fun p : StateDifference Bool Bool => p.base) h
  cases hb

end Diffan.MiddleObservation
