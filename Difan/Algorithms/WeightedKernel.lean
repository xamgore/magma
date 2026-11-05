module

public import Difan.Paths.ChainCount
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.WeightedKernel — algebra of natural-number transition weights

A kernel counts weighted transitions between abstract states. Its composition
is matrix multiplication over Nat. It is always mathematically defined, but
there is NO implicit claim that it equals the DDT of composed functions.
That equality requires a separate fiber-factorization certificate.
-/

namespace Difan

/-- A weighted relation from `A` to `B`; no probability assumptions. -/
abbrev WeightKernel (A B : Type*) := A → B → Nat

/-- Matrix-style composition, summing over the intermediate abstract state. -/
def WeightKernel.comp {A B C : Type*} [Fintype B]
    (p : WeightKernel A B) (q : WeightKernel B C) : WeightKernel A C :=
  fun a c => ∑ b : B, p a b * q b c

/-- The identity kernel contributes one unit when the labels coincide. -/
def WeightKernel.id (A : Type*) [DecidableEq A] : WeightKernel A A :=
  fun a b => if a = b then 1 else 0

/-- Composition of kernels is associative (finite-sum associativity). -/
theorem WeightKernel.comp_assoc {A B C D : Type*}
    [Fintype B] [Fintype C]
    (p : WeightKernel A B) (q : WeightKernel B C)
    (r : WeightKernel C D) :
    WeightKernel.comp (WeightKernel.comp p q) r =
      WeightKernel.comp p (WeightKernel.comp q r) := by
  funext a d
  change
    (∑ c : C, (∑ b : B, p a b * q b c) * r c d) =
      (∑ b : B, p a b * (∑ c : C, q b c * r c d))
  calc
    (∑ c : C, (∑ b : B, p a b * q b c) * r c d) =
        ∑ c : C, ∑ b : B, (p a b * q b c) * r c d := by
      simp_rw [Finset.sum_mul]
    _ = ∑ b : B, ∑ c : C, (p a b * q b c) * r c d := by
      rw [Finset.sum_comm]
    _ = ∑ b : B, ∑ c : C, p a b * (q b c * r c d) := by
      simp_rw [mul_assoc]
    _ = ∑ b : B, p a b * (∑ c : C, q b c * r c d) := by
      simp_rw [Finset.mul_sum]

/-- A kernel is a numerical relation, not a state function. -/
def WeightKernel.support {A B : Type*}
    (p : WeightKernel A B) (a : A) (b : B) : Prop :=
  0 < p a b

end Difan
