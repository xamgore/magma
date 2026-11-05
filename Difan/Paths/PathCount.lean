module

public import Difan.Core.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.PathCount — exact two-step trajectory counting

Stage D: an exact, generic and *quantitative* composition theorem.
For a fixed input difference and output difference, each actual input
state determines ONE intermediate difference. Consequently the full
set of inputs is in bijection with the sigma-type of path witnesses.

The theorem is not a product of DDT coefficients and does not invoke
independence. Predicates P and Q constrain actual concrete states.
-/

namespace Difan

/-- Witnesses of a conditional differential of the composed function.
    The condition `Q` is tested on the *actual* intermediate state. -/
abbrev ComposedFiber {X Y Z A C : Type*}
    (sx : DifferenceSpace X A) (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop) (a : A) (c : C) : Type _ :=
  {x : X // P x ∧ Q (f x) ∧ derivative sx sz (g ∘ f) a x = c}

/-- Witnesses with an explicitly recorded intermediate difference b. -/
abbrev IntermediateFiber {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (b : B) (c : C) : Type _ :=
  {x : X // P x ∧ Q (f x) ∧
    derivative sx sy f a x = b ∧
    derivative sy sz g b (f x) = c}

/-- Every concrete composed witness determines a unique
    intermediate difference. Conversely every refined path gives a
    concrete composed witness. This is a *bijection*, not an estimate. -/
def pathDecomposition {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop) (a : A) (c : C) :
    ComposedFiber sx sz f g P Q a c ≃
      Σ b : B, IntermediateFiber sx sy sz f g P Q a b c where
  toFun w :=
    ⟨derivative sx sy f a w.1,
      ⟨w.1, w.2.1, w.2.2.1, rfl, by
        rw [← derivative_comp sx sy sz f g a w.1]
        exact w.2.2.2⟩⟩
  invFun w :=
    ⟨w.2.1, w.2.2.1, w.2.2.2.1, by
      rw [derivative_comp sx sy sz f g a w.2.1,
        w.2.2.2.2.1]
      exact w.2.2.2.2.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨b, ⟨x, hx⟩⟩
    have hb : derivative sx sy f a x = b := hx.2.2.1
    subst b
    rfl

/-- Number of actual input states satisfying the composed condition.
    This is a mathematical cardinality, not a proposed fast algorithm. -/
noncomputable def composedCount {X Y Z A C : Type*}
    [Fintype X]
    (sx : DifferenceSpace X A) (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop) (a : A) (c : C) : Nat := by
  classical
  exact Fintype.card (ComposedFiber sx sz f g P Q a c)

/-- Number of concrete input states realizing a particular
    intermediate difference (with consistent intermediate state). -/
noncomputable def intermediateCount {X Y Z A B C : Type*}
    [Fintype X]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (b : B) (c : C) : Nat := by
  classical
  exact Fintype.card (IntermediateFiber sx sy sz f g P Q a b c)

/-- EXACT quantitative decomposition into disjoint intermediate
    difference fibers. No independence or multiplication assumption.

    **This is the general theorem that earlier Magma-specific proofs
    could not have stated before a common Difan interface existed.** -/
theorem composedCount_eq_sum_intermediate {X Y Z A B C : Type*}
    [Fintype X] [Fintype B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop) (a : A) (c : C) :
    composedCount sx sz f g P Q a c =
      ∑ b : B, intermediateCount sx sy sz f g P Q a b c := by
  classical
  unfold composedCount intermediateCount
  calc
    Fintype.card (ComposedFiber sx sz f g P Q a c) =
        Fintype.card (Σ b : B,
          IntermediateFiber sx sy sz f g P Q a b c) :=
      Fintype.card_congr (pathDecomposition sx sy sz f g P Q a c)
    _ = _ := by simp only [Fintype.card_sigma]

/-- Without any state preconditions, the composed count *is* the
    ordinary DDT of the composed function. -/
theorem composedCount_true_eq_ddt {X Y Z A C : Type*}
    [Fintype X] [DecidableEq C]
    (sx : DifferenceSpace X A) (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C) :
    composedCount sx sz f g (fun _ => True) (fun _ => True) a c =
      ddt sx sz (g ∘ f) a c := by
  classical
  simp [composedCount, ddt, Fintype.card_subtype]

/-- The universal exact two-stage DDT decomposition. Notice that
    each term is a count of *joint concrete trajectories*, not a
    product of independently counted one-stage DDT coefficients. -/
theorem ddt_comp_eq_sum_actual_paths {X Y Z A B C : Type*}
    [Fintype X] [Fintype B] [DecidableEq C]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C) :
    ddt sx sz (g ∘ f) a c =
      ∑ b : B, intermediateCount sx sy sz f g
        (fun _ => True) (fun _ => True) a b c := by
  calc
    ddt sx sz (g ∘ f) a c =
        composedCount sx sz f g (fun _ => True) (fun _ => True) a c :=
      (composedCount_true_eq_ddt sx sz f g a c).symm
    _ = _ := composedCount_eq_sum_intermediate sx sy sz f g
      (fun _ => True) (fun _ => True) a c

end Difan
