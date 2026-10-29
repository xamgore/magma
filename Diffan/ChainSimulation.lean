module

public import Diffan.ChainCount
public import Diffan.Simulation
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.ChainSimulation — composition of exact abstract simulations

An abstract state is suitable for a chain if every concrete step respects
it. A commuting diagram is enough for exact abstract evolution; it is
not enough to infer equality of fiber cardinalities.
-/

namespace Diffan

/-- A list of matched concrete/abstract transitions. The predicate is
    local to each step and can be proved independently per algorithm. -/
theorem simulation_chain {X A : Type*}
    (observe : X → A)
    (steps : List ((X → X) × (A → A))) :
    (∀ p ∈ steps, ∀ x, observe (p.1 x) = p.2 (observe x)) →
      ∀ x, observe ((⟨steps.map Prod.fst⟩ : Chain X).run x) =
        (⟨steps.map Prod.snd⟩ : Chain A).run (observe x) := by
  induction steps with
  | nil =>
      intro _ x
      rfl
  | cons p rest ih =>
      intro h x
      have hhead : ∀ x, observe (p.1 x) = p.2 (observe x) :=
        h p (by simp)
      have htail : ∀ q ∈ rest, ∀ x,
          observe (q.1 x) = q.2 (observe x) := by
        intro q hq
        exact h q (by simp [hq])
      change observe ((⟨rest.map Prod.fst⟩ : Chain X).run (p.1 x)) =
        (⟨rest.map Prod.snd⟩ : Chain A).run (p.2 (observe x))
      rw [ih htail (p.1 x), hhead x]

end Diffan
