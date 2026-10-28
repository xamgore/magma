module

public import Diffan.Conditional
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Simulation

The full pair of concrete states composes exactly. A smaller abstract
state composes exactly only after a simulation/commuting law has been
proved. Such a law alone does NOT imply preservation of fiber counts.
-/

namespace Diffan

/-- Exact transport of a pair of concrete states. -/
def pairMap {X Y : Type*} (f : X → Y) : X × X → Y × Y :=
  fun xy => (f xy.1, f xy.2)

/-- Ordinary function composition is exact on *pairs of states*. -/
theorem pairMap_comp {X Y Z : Type*}
    (f : X → Y) (g : Y → Z) :
    pairMap (g ∘ f) = pairMap g ∘ pairMap f := by
  rfl

/-- A proved exact abstraction of a deterministic transformation.
    `observe` must retain whatever information makes the step sound. -/
structure StepSimulation (X A : Type*) (f : X → X) where
  observe : X → A
  step : A → A
  correct : ∀ x, observe (f x) = step (observe x)

/-- If two steps respect the same observation, their abstract steps
    compose exactly, with no probabilistic independence assumption. -/
theorem step_simulation_comp {X A : Type*}
    (observe : X → A) (f g : X → X) (F G : A → A)
    (hf : ∀ x, observe (f x) = F (observe x))
    (hg : ∀ x, observe (g x) = G (observe x))
    (x : X) :
    observe ((g ∘ f) x) = (G ∘ F) (observe x) := by
  simp only [Function.comp_apply, hg, hf]

/-- A certificate for exact *counts* must be stated independently of
    exact abstract-state evolution: collapsing distinct states may change
    multiplicities. -/
structure CountCertificate {K A B : Type*}
    (trueCount : K → A → B → Nat) where
  abstractCount : K → A → B → Nat
  correct : ∀ k a b, abstractCount k a b = trueCount k a b

end Diffan
