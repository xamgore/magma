module

public import Difan.Composition.Composition
public import Difan.Core.StateDifference
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.Conditional

Exact support remembers a concrete base state. A differential `(a,b)` is
not, by itself, a composable execution witness. `P` and `Q` constrain
actual base states before and between transformations.
-/

namespace Difan

/-- A selected differential with a predicate on its input base state. -/
structure ConditionalTransition (X A B : Type*) where
  input : A
  output : B
  pre : X → Prop

/-- A conditional transition is possible if a concrete state realizes it. -/
def conditionalSupport {X Y A B : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (f : X → Y) (t : ConditionalTransition X A B) : Prop :=
  ∃ x,
    let p : StateDifference X A := ⟨x, t.input⟩
    t.pre p.base ∧ (p.transport sx sy f).delta = t.output

/-- A Hoare-style guarantee uses a universal condition on all inputs. -/
def preserves {X Y : Type*}
    (f : X → Y) (P : X → Prop) (Q : Y → Prop) : Prop :=
  ∀ x, P x → Q (f x)

/-- Actual two-stage differential path, keeping the *same* intermediate
    state `f x` in both stages. -/
def exactPath {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (b : B) (c : C) : Prop :=
  ∃ x,
    let initial : StateDifference X A := ⟨x, a⟩
    let intermediate := initial.transport sx sy f
    P initial.base ∧ Q intermediate.base ∧ intermediate.delta = b ∧
      ((⟨intermediate.base, b⟩ : StateDifference Y B).transport sy sz g).delta = c

/-- Exact composition quantified over the intermediate *difference and
    base state*. This is an equivalence, not a loose support inclusion. -/
theorem composed_conditional_iff_exact_path
    {X Y Z A B C : Type*}
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (c : C) :
    (∃ x, P x ∧ Q (f x) ∧
      derivative sx sz (g ∘ f) a x = c) ↔
    ∃ b, exactPath sx sy sz f g P Q a b c := by
  constructor
  · rintro ⟨x, hP, hQ, hcomp⟩
    refine ⟨derivative sx sy f a x, x, hP, hQ, rfl, ?_⟩
    rw [derivative_comp sx sy sz f g a x] at hcomp
    exact hcomp
  · rintro ⟨b, x, hP, hQ, hb, hc⟩
    change derivative sx sy f a x = b at hb
    change derivative sy sz g b (f x) = c at hc
    refine ⟨x, hP, hQ, ?_⟩
    rw [derivative_comp sx sy sz f g a x, hb]
    exact hc

end Difan
