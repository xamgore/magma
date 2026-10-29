module

public import Diffan.Constraints
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Composition — relational overapproximation versus exact counts

Exact composition of state functions always exists. The composition of their
*difference supports* is in general only an overapproximation.
A numerical factorization requires an additional theorem, not a `mul` method.
-/

namespace Diffan

/-- Relational composition of possible transitions, via an intermediate difference. -/
def composeSupport {A B C : Type*}
    (r : A → B → Prop) (s : B → C → Prop) : A → C → Prop :=
  fun a c => ∃ b, r a b ∧ s b c

/-- Every realized composed transition has a compatible *difference path*.
    The reverse implication is false in general, because base points may differ. -/
theorem support_comp_subset {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B) (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C) :
    support sx sz (g ∘ f) a c →
      composeSupport (support sx sy f) (support sy sz g) a c := by
  rintro ⟨x, hx⟩
  refine ⟨derivative sx sy f a x, ⟨x, rfl⟩, ⟨f x, ?_⟩⟩
  rw [← derivative_comp sx sy sz f g a x]
  exact hx

/-- If no abstract difference path exists, the actual transition is impossible. -/
theorem impossible_of_no_support_path {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z) (a : A) (c : C)
    (h : ¬ composeSupport (support sx sy f) (support sy sz g) a c) :
    ¬ support sx sz (g ∘ f) a c := by
  intro actual
  exact h (support_comp_subset sx sy sz f g a c actual)

/-- A formula for exact composed counts is a separate *certified object*.
    In particular, this interface does NOT assume multiplication of DDTs. -/
structure ExactCompositionFormula {K A B : Type*}
    (trueCount : K → A → B → Nat) where
  formula : K → A → B → Nat
  correct : ∀ k a b, trueCount k a b = formula k a b

/-- A PRODUCT formula must supply its own proof. Merely knowing the two
    factors or their individual supports is not enough. -/
structure ProductFactorization {K A B : Type*}
    (trueCount : K → A → B → Nat) where
  leftFactor : K → A → B → Nat
  rightFactor : K → A → B → Nat
  correct : ∀ k a b,
    trueCount k a b = leftFactor k a b * rightFactor k a b

end Diffan
