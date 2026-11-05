module

public import Difan.Paths.Chain
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.ChainCount — exact finite partitions of n-step DDT

Any finite observation of an entire trajectory partitions the *actual*
input witnesses into disjoint fibers. No product of marginal DDT entries
is asserted; the same original state is retained in every fiber.
-/

namespace Difan

/-- Conditional final-path predicate. `Q` examines the actual final
    base state (not merely the final difference). -/
def admissibleChain {X A : Type*}
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (p : StateDifference X A) (b : A) : Prop :=
  let final := c.propagateState s p
  P p.base ∧ Q final.base ∧ final.delta = b

/-- Exact number of admissible initial states. -/
noncomputable def chainCount {X A : Type*} [Fintype X]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) : Nat := by
  classical
  exact Fintype.card {x : X // admissibleChain s c P Q ⟨x, a⟩ b}

/-- Exact number of admitted initial states with a chosen finite label.
    The label can be the full state, the sequence of differences, or
    a certified abstract observation (e.g. a carry state). -/
noncomputable def labeledChainCount {X A L : Type*} [Fintype X]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A)
    (label : X → L) (l : L) : Nat := by
  classical
  exact Fintype.card
    {x : X // admissibleChain s c P Q ⟨x, a⟩ b ∧ label x = l}

/-- Every admitted state belongs to a *unique* label fiber. -/
def chainFiberEquiv {X A L : Type*}
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L) :
    {x : X // admissibleChain s c P Q ⟨x, a⟩ b} ≃
      Σ l : L, {x : X // admissibleChain s c P Q ⟨x, a⟩ b ∧ label x = l} where
  toFun w := ⟨label w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun w := ⟨w.2.1, w.2.2.1⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨l, ⟨x, hx⟩⟩
    have heq : label x = l := hx.2
    cases heq
    rfl

/-- Universal *exact* quantitative partition for any finite label type.
    This is a mathematical theorem, not a claim of fast evaluation. -/
theorem chainCount_eq_sum_labels {X A L : Type*}
    [Fintype X] [Fintype L]
    (s : DifferenceSpace X A) (c : Chain X)
    (P Q : X → Prop) (a b : A) (label : X → L) :
    chainCount s c P Q a b =
      ∑ l : L, labeledChainCount s c P Q a b label l := by
  classical
  unfold chainCount labeledChainCount
  calc
    Fintype.card {x : X // admissibleChain s c P Q ⟨x, a⟩ b} =
        Fintype.card
          (Σ l : L, {x : X // admissibleChain s c P Q ⟨x, a⟩ b ∧
            label x = l}) :=
      Fintype.card_congr (chainFiberEquiv s c P Q a b label)
    _ = _ := by simp only [Fintype.card_sigma]

/-- With trivial preconditions, the exact chain count is the ordinary
    DDT of its actual composed transformation. -/
theorem chainCount_true_eq_ddt {X A : Type*}
    [Fintype X] [DecidableEq A]
    (s : DifferenceSpace X A) (c : Chain X) (a b : A) :
    chainCount s c (fun _ => True) (fun _ => True) a b =
      ddt s s c.run a b := by
  classical
  simp [chainCount, admissibleChain, Chain.propagateState_delta,
    ddt, Fintype.card_subtype]

/-- **n-step DDT composition**: partition the actual witnesses by their
    entire sequence of intermediate differences.

    This is exact for arbitrary deterministic chains and does not treat
    separate-round DDTs as independent. The sum is a specification,
    NOT a proposed efficient algorithm when n is large. -/
theorem ddt_chain_eq_sum_signatures {X A : Type*}
    [Fintype X] [Fintype A] [DecidableEq A]
    (s : DifferenceSpace X A) (c : Chain X) (a b : A) :
    ddt s s c.run a b =
      ∑ sig : (Fin c.steps.length → Option A),
        labeledChainCount s c (fun _ => True) (fun _ => True)
          a b (c.signature s a) sig := by
  calc
    ddt s s c.run a b =
        chainCount s c (fun _ => True) (fun _ => True) a b :=
      (chainCount_true_eq_ddt s c a b).symm
    _ = _ := chainCount_eq_sum_labels s c (fun _ => True)
      (fun _ => True) a b (c.signature s a)

end Difan
