module
public import Diffan.Algorithms.WeightedKernel
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.TwistedConditionalGram — exact self-join of one state-labelled kernel

This is an algebraic identity for arbitrary finite labels. The label
u is a SHARED concrete intermediate base; no products of unconditioned
DDT marginals occur. Sigma and tau may be arbitrary functions
(they are a half-swap and its difference action for Magma).
-/

namespace Diffan.TwistedConditionalGram

variable {U A D : Type*}

/-- A deterministic conditional derivative response from a
specific intermediate base u to output difference lambda. -/
def oneHot [DecidableEq D] (deriv : U → A → D) (u : U) (a : A) (lambda : D) : Nat :=
  if deriv u a = lambda then 1 else 0

/-- Twisted correlation of TWO copies of the SAME conditional kernel.
The second one is evaluated at the actual transformed base sigma(u),
with the same intermediate difference lambda acted on by tau. -/
def gram [Fintype U] [Fintype D] [DecidableEq D]
    (deriv : U → A → D) (sigma : U → U) (tau : D → D)
    (a b : A) : Nat :=
  ∑ u : U, ∑ lambda : D,
    oneHot deriv u a lambda *
      oneHot deriv (sigma u) b (tau lambda)

/-- Exact contraction of the lambda variable: it is a functional
output label, not an extra witness to count. This works
for any finite U,D and any (possibly nonlinear) sigma,tau. -/
theorem gram_eq_matching_base_count
    [Fintype U] [Fintype D] [DecidableEq D]
    (deriv : U → A → D) (sigma : U → U) (tau : D → D)
    (a b : A) :
    gram deriv sigma tau a b =
      ((Finset.univ : Finset U).filter
        (fun u => deriv (sigma u) b = tau (deriv u a))).card := by
  classical
  unfold gram oneHot
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Fintype.sum_ite_eq]
  rw [Finset.card_filter]

end Diffan.TwistedConditionalGram
