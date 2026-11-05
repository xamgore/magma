module

public import Difan.Algorithms.WeightedKernel
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.CertifiedFibers — exact weights of abstract trajectory fibers

A label is cheap to manipulate only when its fiber count is known by a
separate correctness certificate. Here we distinguish:
* a proposed weight per abstract label;
* the proof that it is the cardinality of the actual labeled fiber;
* an optional equivalence of that fiber with a smaller concrete model.

This provides a quantitative interface over the exact ChainCount laws.
-/

namespace Difan

/-- Attach certified numeric weights to abstract labels of whole trajectories. -/
structure ChainWeightCertificate {X A L : Type*}
    [Fintype X] [Fintype L]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L) where
  weight : L → Nat
  correct : ∀ l, weight l = labeledChainCount s c P Q a b label l

/-- Once each abstract weight is certified, the chain count is exactly
    their sum. There is no claim of efficient evaluation unless `weight`
    itself has a tractable formula. -/
theorem chainCount_eq_sum_certified {X A L : Type*}
    [Fintype X] [Fintype L]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L)
    (cert : ChainWeightCertificate s c P Q a b label) :
    chainCount s c P Q a b = ∑ l : L, cert.weight l := by
  rw [chainCount_eq_sum_labels s c P Q a b label]
  apply Finset.sum_congr rfl
  intro l _
  exact (cert.correct l).symm

/-- A *fiber model* gives a bijection between each real trajectory fiber
    and a more compactly described mathematical type of the SAME cardinality. This is stronger
    than a simulation theorem, which need not preserve cardinalities. -/
structure ChainFiberModel {X A L : Type*}
    [Fintype X] [Fintype L]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L) where
  Small : L → Type*
  smallFinite : ∀ l, Fintype (Small l)
  equiv : ∀ l,
    {x : X // admissibleChain s c P Q ⟨x, a⟩ b ∧ label x = l} ≃ Small l

/-- Fiber equivalences can replace a large-state count with a sum of
    more tractable model cardinalities. This is a symbolic theorem, not a big
    computation of `Fintype X`. -/
theorem chainCount_eq_sum_small {X A L : Type*}
    [Fintype X] [Fintype L]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L)
    (model : ChainFiberModel s c P Q a b label) :
    chainCount s c P Q a b =
      ∑ l : L, @Fintype.card (model.Small l) (model.smallFinite l) := by
  classical
  rw [chainCount_eq_sum_labels s c P Q a b label]
  apply Finset.sum_congr rfl
  intro l _
  let : Fintype (model.Small l) := model.smallFinite l
  change
    Fintype.card
      {x : X // admissibleChain s c P Q ⟨x, a⟩ b ∧ label x = l} =
      Fintype.card (model.Small l)
  exact Fintype.card_congr (model.equiv l)

end Difan
