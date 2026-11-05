module

import all Init.Data.Range.Basic
public import Diffan.Composition.Meet

@[expose] public section

/-!
# Exact two-sided matching over a shared parameter

The two halves of an execution use the same parameter, which can be a
master key. Endpoint predicates constrain the initial and final objects;
a middle predicate constrains the full intermediate object, such as a
concrete base state together with its difference.

The endpoint-to-joined witness bijection acts separately at each parameter.
Taking their dependent sum gives a partition of all compatible witnesses
by parameter, preserving exact cardinalities.
-/

namespace Diffan.KeyedMeet

variable {K I S O : Type*}

/-- Endpoint witnesses for one master parameter, with a constraint on
    the actual intermediate object `left k i`. -/
abbrev Endpoints
    (left : K → I ≃ S) (right : K → S ≃ O)
    (P : K → I → Prop) (Q : K → O → Prop)
    (R : K → S → Prop) : Type _ :=
  Σ k : K,
    Meet.EndpointFiber (left k) (right k)
      (fun i => P k i ∧ R k ((left k) i)) (Q k)

/-- Equivalent witnesses retaining both endpoints and the proof of
    exact agreement at the same intermediate object. -/
abbrev Joined
    (left : K → I ≃ S) (right : K → S ≃ O)
    (P : K → I → Prop) (Q : K → O → Prop)
    (R : K → S → Prop) : Type _ :=
  Σ k : K,
    Meet.JoinedFiber (left k) (right k)
      (fun i => P k i ∧ R k ((left k) i)) (Q k)

/-- Fiberwise matching extends to a shared key without ever introducing
    separate independent parameters for the two halves. -/
def fiberEquiv
    (left : K → I ≃ S) (right : K → S ≃ O)
    (P : K → I → Prop) (Q : K → O → Prop)
    (R : K → S → Prop) :
    Endpoints left right P Q R ≃ Joined left right P Q R where
  toFun := fun ⟨k, w⟩ =>
    ⟨k, (Meet.fiberEquiv (left k) (right k)
      (fun i => P k i ∧ R k ((left k) i)) (Q k)) w⟩
  invFun := fun ⟨k, w⟩ =>
    ⟨k, (Meet.fiberEquiv (left k) (right k)
      (fun i => P k i ∧ R k ((left k) i)) (Q k)).symm w⟩
  left_inv := by
    rintro ⟨k, w⟩
    simp
  right_inv := by
    rintro ⟨k, w⟩
    simp

open scoped Classical in
/-- Exact count of compatible endpoint pairs and concrete witnesses.
    This identity is unconditional for the given keyed equivalences. -/
theorem card_joined_eq_endpoints
    [Fintype K] [Fintype I] [Fintype O]
    (left : K → I ≃ S) (right : K → S ≃ O)
    (P : K → I → Prop) (Q : K → O → Prop)
    (R : K → S → Prop) :
    Fintype.card (Joined left right P Q R) =
      Fintype.card (Endpoints left right P Q R) := by
  classical
  exact Fintype.card_congr (fiberEquiv left right P Q R).symm

open scoped Classical in
/-- Exact sum over the SAME master parameter. This is a fiber partition,
    not a product of independent-key DDTs. -/
theorem card_joined_eq_sum_by_key
    [Fintype K] [Fintype I] [Fintype O]
    (left : K → I ≃ S) (right : K → S ≃ O)
    (P : K → I → Prop) (Q : K → O → Prop)
    (R : K → S → Prop) :
    Fintype.card (Joined left right P Q R) =
      ∑ k : K, Fintype.card
        (Meet.EndpointFiber (left k) (right k)
          (fun i => P k i ∧ R k ((left k) i)) (Q k)) := by
  classical
  rw [card_joined_eq_endpoints]
  simp only [Endpoints, Fintype.card_sigma]

end Diffan.KeyedMeet
