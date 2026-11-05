module

import all Init.Data.Range.Basic
public import Diffan.Composition.Meet

@[expose] public section

/-!
# Exact transport of meeting fibers

A numerical equality between two meet counts is justified by an equivalence
of their *actual* witness fibers.  The certificate below records a commuting
square on both sides of the full midpoint and preservation of three
predicates.  Equality of marginal DDTs, or matching difference-only labels,
is not substituted for these hypotheses.

The theorem is polymorphic in the endpoint and midpoint types.  The two
systems may also differ in their endpoint and midpoint predicates.
-/

namespace Diffan.MeetFiberTransport

variable {I S O : Type*}

/-- A proof-carrying change of coordinates between two exact meets. -/
structure Certificate
    (left₀ left₁ : I ≃ S) (right₀ right₁ : S ≃ O)
    (P₀ P₁ : I → Prop) (Q₀ Q₁ : O → Prop)
    (R₀ R₁ : S → Prop) where
  input : I ≃ I
  middle : S ≃ S
  output : O ≃ O
  left_comm : ∀ i, left₁ (input i) = middle (left₀ i)
  right_comm : ∀ s, right₁ (middle s) = output (right₀ s)
  initial_iff : ∀ i, P₁ (input i) ↔ P₀ i
  final_iff : ∀ o, Q₁ (output o) ↔ Q₀ o
  middle_iff : ∀ s, R₁ (middle s) ↔ R₀ s

/-- Both halves together commute with the endpoint coordinate changes. -/
theorem Certificate.full_comm
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁)
    (i : I) :
    right₁ (left₁ (c.input i)) = c.output (right₀ (left₀ i)) := by
  rw [c.left_comm i, c.right_comm (left₀ i)]

/-- A genuine meet is transported to a genuine meet, in both directions. -/
theorem Certificate.meets_iff
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁)
    (i : I) (o : O) :
    Meet.meets left₀ right₀ i o ↔
      Meet.meets left₁ right₁ (c.input i) (c.output o) := by
  rw [Meet.meets_iff, Meet.meets_iff, c.full_comm i]
  constructor
  · intro h
    rw [h]
  · intro h
    exact c.output.injective h

/-- The entire endpoint admissibility condition is preserved at once. -/
theorem Certificate.admissible_iff
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁)
    (i : I) :
    (P₁ (c.input i) ∧ R₁ (left₁ (c.input i))) ∧
      Q₁ (right₁ (left₁ (c.input i))) ↔
    (P₀ i ∧ R₀ (left₀ i)) ∧ Q₀ (right₀ (left₀ i)) := by
  rw [c.left_comm i, c.right_comm (left₀ i)]
  exact and_congr
    (and_congr (c.initial_iff i) (c.middle_iff (left₀ i)))
    (c.final_iff (right₀ (left₀ i)))

/-- A *concrete* equivalence of the endpoint fibers: no independent paths. -/
def Certificate.endpointEquiv
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁) :
    Meet.EndpointFiber left₀ right₀
      (fun i => P₀ i ∧ R₀ (left₀ i)) Q₀ ≃
    Meet.EndpointFiber left₁ right₁
      (fun i => P₁ i ∧ R₁ (left₁ i)) Q₁ where
  toFun := fun w => ⟨c.input w.1, (c.admissible_iff w.1).mpr w.2⟩
  invFun := fun w =>
    ⟨c.input.symm w.1, (c.admissible_iff (c.input.symm w.1)).mp
      (by simpa only [Equiv.apply_symm_apply] using w.2)⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact c.input.symm_apply_apply w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact c.input.apply_symm_apply w.1

/-- The joined, two-endpoint witnesses have the same cardinality too. -/
def Certificate.joinedEquiv
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁) :
    Meet.JoinedFiber left₀ right₀
      (fun i => P₀ i ∧ R₀ (left₀ i)) Q₀ ≃
    Meet.JoinedFiber left₁ right₁
      (fun i => P₁ i ∧ R₁ (left₁ i)) Q₁ :=
  ((Meet.fiberEquiv left₀ right₀
    (fun i => P₀ i ∧ R₀ (left₀ i)) Q₀).symm).trans
      (c.endpointEquiv.trans
        (Meet.fiberEquiv left₁ right₁
          (fun i => P₁ i ∧ R₁ (left₁ i)) Q₁))

open scoped Classical in
/-- Exact quantitative invariance follows from the actual fiber bijection. -/
theorem Certificate.card_joined_eq
    [Fintype I] [Fintype O]
    {left₀ left₁ : I ≃ S} {right₀ right₁ : S ≃ O}
    {P₀ P₁ : I → Prop} {Q₀ Q₁ : O → Prop}
    {R₀ R₁ : S → Prop}
    (c : Certificate left₀ left₁ right₀ right₁ P₀ P₁ Q₀ Q₁ R₀ R₁) :
    Fintype.card (Meet.JoinedFiber left₀ right₀
      (fun i => P₀ i ∧ R₀ (left₀ i)) Q₀) =
    Fintype.card (Meet.JoinedFiber left₁ right₁
      (fun i => P₁ i ∧ R₁ (left₁ i)) Q₁) := by
  classical
  exact Fintype.card_congr c.joinedEquiv

end Diffan.MeetFiberTransport
