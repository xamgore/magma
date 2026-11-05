module

import all Init.Data.Range.Basic
public import Diffan.Paths.ReversibleChain

@[expose] public section

/-!
# Diffan.Meet — exact agreement at a shared intermediate state

Given two equivalences `left : I ≃ M` and `right : M ≃ O`, a forward
candidate `i : I` and a backward candidate `o : O` meet if and only if
both reach the SAME `m : M`.

Unlike comparison of difference-only supports, this remembers the full
intermediate object. Instantiate `M` with `StateDifference X Δ` to
retain both the concrete base state and its difference.
-/

namespace Diffan.Meet

/-- Two endpoint candidates agree on their actual intermediate object. -/
def meets {I M O : Type*}
    (left : I ≃ M) (right : M ≃ O) (i : I) (o : O) : Prop :=
  left i = right.symm o

/-- Exact meet is equivalent to belonging to one complete execution.
    There is no approximation: the intermediate object is identical. -/
theorem meets_iff {I M O : Type*}
    (left : I ≃ M) (right : M ≃ O) (i : I) (o : O) :
    meets left right i o ↔ right (left i) = o := by
  constructor
  · intro h
    rw [meets] at h
    rw [h]
    exact right.apply_symm_apply o
  · intro h
    apply right.injective
    simpa only [Equiv.apply_symm_apply] using h

/-- State predicates are checked at the real endpoints, while the
    intermediate equality is checked on the entire middle object. -/
abbrev EndpointFiber {I M O : Type*}
    (left : I ≃ M) (right : M ≃ O)
    (P : I → Prop) (Q : O → Prop) : Type _ :=
  {i : I // P i ∧ Q (right (left i))}

/-- A two-sided witness retains both endpoints and the proof that they
    meet at the *same* intermediate object. -/
abbrev JoinedFiber {I M O : Type*}
    (left : I ≃ M) (right : M ≃ O)
    (P : I → Prop) (Q : O → Prop) : Type _ :=
  {io : I × O // P io.1 ∧ Q io.2 ∧ meets left right io.1 io.2}

/-- No endpoint pairs are invented or counted twice when joining.
    The final endpoint is uniquely determined by the initial endpoint. -/
def fiberEquiv {I M O : Type*}
    (left : I ≃ M) (right : M ≃ O)
    (P : I → Prop) (Q : O → Prop) :
    EndpointFiber left right P Q ≃ JoinedFiber left right P Q where
  toFun w := ⟨(w.1, right (left w.1)), ⟨w.2.1, w.2.2, by
    simp only [meets, Equiv.symm_apply_apply]⟩⟩
  invFun w := ⟨w.1.1, ⟨w.2.1, by
    have h := (meets_iff left right w.1.1 w.1.2).mp w.2.2.2
    rw [h]
    exact w.2.2.1⟩⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (meets_iff left right w.1.1 w.1.2).mp w.2.2.2

open scoped Classical in
/-- The shared midpoint bijection preserves the number of endpoint witnesses. -/
theorem card_joined_eq_card_endpoints {I M O : Type*}
    [Fintype I] [Fintype O]
    (left : I ≃ M) (right : M ≃ O)
    (P : I → Prop) (Q : O → Prop) :
    Fintype.card (JoinedFiber left right P Q) =
      Fintype.card (EndpointFiber left right P Q) := by
  classical
  exact Fintype.card_congr (fiberEquiv left right P Q).symm

end Diffan.Meet
