module

import all Init.Data.Range.Basic
public import Diffan.Meet

@[expose] public section

/-!
# Diffan.ReversibleMeet — the same middle StateDifference, from both sides

Split a reversible chain into `prefixChain` followed by `suffixChain`. Forward
propagation of the initial pair through `prefixChain` and backward
propagation of the final pair through `suffixChain` must agree on the WHOLE
`StateDifference`, not just its `delta` component.

This gives an exact meet-in-the-middle criterion for concrete pairs.
-/

namespace Diffan.ReversibleMeet

/-- A reversible chain induces an exact bijection on pairs of states
    represented as a base point plus its difference. -/
def pairEquiv {X A : Type*}
    (s : DifferenceSpace X A) (c : ReversibleChain X) :
    StateDifference X A ≃ StateDifference X A :=
  StateDifference.transportEquiv s s c.toEquiv

/-- Two reversible chain halves meet at precisely the same concrete
    base state and difference. -/
def meets {X A : Type*}
    (s : DifferenceSpace X A)
    (prefixChain suffixChain : ReversibleChain X)
    (p q : StateDifference X A) : Prop :=
  Meet.meets (pairEquiv s prefixChain) (pairEquiv s suffixChain) p q

/-- Agreement at the split is exactly successful forward propagation
    through both halves. -/
theorem meets_iff_forward {X A : Type*}
    (s : DifferenceSpace X A)
    (prefixChain suffixChain : ReversibleChain X)
    (p q : StateDifference X A) :
    meets s prefixChain suffixChain p q ↔
      StateDifference.transport s s (prefixChain.append suffixChain).forward.run p = q := by
  rw [meets, Meet.meets_iff]
  have hrun : (prefixChain.append suffixChain).forward.run =
      suffixChain.forward.run ∘ prefixChain.forward.run := by
    funext x
    exact Chain.run_append prefixChain.forward suffixChain.forward x
  rw [hrun]
  change
    StateDifference.transport s s suffixChain.forward.run
        (StateDifference.transport s s prefixChain.forward.run p) = q ↔
      StateDifference.transport s s
        (suffixChain.forward.run ∘ prefixChain.forward.run) p = q
  rw [← StateDifference.transport_comp]

end Diffan.ReversibleMeet
