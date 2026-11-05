module

import all Init.Data.Range.Basic
public import Diffan.Core.Differential

@[expose] public section

/-!
# Diffan.CoordinateSeparation — exact product fibers

A bijective change of coordinates does *not by itself* prove numerical
factorization. The missing hypothesis is that the predicate on actual
witnesses separates as `P u ∧ Q v` in the new coordinates.

Once this is proved, the two certified fibers form a Cartesian product,
and their cardinalities multiply. This is the structural principle used
by the specialized three-round Magma factorization.
-/

namespace Diffan.CoordinateSeparation

variable {X U V : Type*}

/-- An explicit bijection between an actual witness fiber and the product
    of two independent-coordinate fibers. -/
def fiberEquiv
    (coordinates : X ≃ U × V)
    (R : X → Prop) (P : U → Prop) (Q : V → Prop)
    (separates : ∀ x, R x ↔ P (coordinates x).1 ∧ Q (coordinates x).2) :
    {x : X // R x} ≃ {u : U // P u} × {v : V // Q v} where
  toFun := fun x =>
    let hs := (separates x.1).mp x.2
    (⟨(coordinates x.1).1, hs.1⟩,
     ⟨(coordinates x.1).2, hs.2⟩)
  invFun := fun uv =>
    ⟨coordinates.symm (uv.1.1, uv.2.1),
      (separates _).mpr (by
        simpa only [Equiv.apply_symm_apply] using
          (And.intro uv.1.2 uv.2.2))⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact coordinates.symm_apply_apply x.1
  right_inv := by
    rintro ⟨u, v⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (coordinates.apply_symm_apply (u.1, v.1))
    · apply Subtype.ext
      exact congrArg Prod.snd (coordinates.apply_symm_apply (u.1, v.1))

open scoped Classical in
/-- Separating the witness predicate in product coordinates factors its cardinality. -/
theorem card_eq_mul
    [Fintype X] [Fintype U] [Fintype V]
    (coordinates : X ≃ U × V)
    (R : X → Prop) (P : U → Prop) (Q : V → Prop)
    (separates : ∀ x, R x ↔ P (coordinates x).1 ∧ Q (coordinates x).2) :
    Fintype.card {x : X // R x} =
      Fintype.card {u : U // P u} * Fintype.card {v : V // Q v} := by
  classical
  calc
    Fintype.card {x : X // R x} =
        Fintype.card ({u : U // P u} × {v : V // Q v}) :=
      Fintype.card_congr (fiberEquiv coordinates R P Q separates)
    _ = _ := by simp only [Fintype.card_prod]

end Diffan.CoordinateSeparation
