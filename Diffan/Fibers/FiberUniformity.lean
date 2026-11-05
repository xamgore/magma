module

import all Init.Data.Range.Basic
public import Diffan.Fibers.FiberDefect

@[expose] public section

/-!
# Diffan.FiberUniformity — exact slices of a two-coordinate witness fiber

No independence is assumed. A joint condition on (r,z) is first counted at
fixed r, then grouped by an arbitrary label c = classify r.

If the *actual conditional cardinality* of the z-fiber is constant on
all r with a given label c, the inner sum factors as

  (number of r with label c) * (common conditional cardinality).

This is a sufficient hypothesis with explicit witnesses, not an automatic
factorization of DDTs.
-/

namespace Diffan.FiberUniformity

/-- Number of actual second-coordinate witnesses at a fixed first
    coordinate, satisfying both the structural and final conditions. -/
noncomputable def conditionalCount {R Z : Type*} [Fintype Z]
    (allowed final : R → Z → Prop) (r : R) : Nat := by
  classical
  exact ((Finset.univ : Finset Z).filter
    (fun z => allowed r z ∧ final r z)).card

open scoped Classical in
/-- Exact decomposition of a joint fiber into its first-coordinate slices,
    then regrouping by any finite label of the first coordinate. -/
theorem card_eq_sum_slices
    {R Z C : Type*} [Fintype R] [Fintype Z] [Fintype C]
    (allowed final : R → Z → Prop) (classify : R → C) :
    ((Finset.univ : Finset (R × Z)).filter
      (fun p => allowed p.1 p.2 ∧ final p.1 p.2)).card =
    ∑ c : C, ∑ r : R,
      if classify r = c then conditionalCount allowed final r else 0 := by
  classical
  calc
    ((Finset.univ : Finset (R × Z)).filter
        (fun p => allowed p.1 p.2 ∧ final p.1 p.2)).card =
        ∑ r : R, conditionalCount allowed final r := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      rw [conditionalCount, Finset.card_filter]
    _ = ∑ r : R, ∑ c : C,
          if classify r = c then conditionalCount allowed final r else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      simp
    _ = ∑ c : C, ∑ r : R,
          if classify r = c then conditionalCount allowed final r else 0 := by
      rw [Finset.sum_comm]

open scoped Classical in
/-- If conditional fiber cardinalities are uniform inside each class,
    regrouping becomes a genuine product of cardinalities. This theorem
    does NOT assert that such uniformity holds for arbitrary maps. -/
theorem card_eq_sum_mul_of_uniform
    {R Z C : Type*} [Fintype R] [Fintype Z] [Fintype C]
    (allowed final : R → Z → Prop) (classify : R → C)
    (weight : C → Nat)
    (uniform : ∀ c r, classify r = c →
      conditionalCount allowed final r = weight c) :
    ((Finset.univ : Finset (R × Z)).filter
      (fun p => allowed p.1 p.2 ∧ final p.1 p.2)).card =
      ∑ c : C, ((Finset.univ : Finset R).filter
        (fun r => classify r = c)).card * weight c := by
  classical
  rw [card_eq_sum_slices allowed final classify]
  apply Finset.sum_congr rfl
  intro c _
  calc
    (∑ r : R, if classify r = c then conditionalCount allowed final r else 0) =
        ∑ r : R, if classify r = c then weight c else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : classify r = c
      · simp only [ite_eq_left h]
        exact uniform c r h
      · simp only [ite_eq_right h]
    _ = ((Finset.univ : Finset R).filter
          (fun r => classify r = c)).card * weight c := by
      rw [Finset.card_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : classify r = c <;> simp [h]

end Diffan.FiberUniformity
