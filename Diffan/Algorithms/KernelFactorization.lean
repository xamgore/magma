module

public import Diffan.Fibers.CertifiedFibers
public import Diffan.Paths.PathCount
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.KernelFactorization — a certified bridge to matrix convolution

For a deterministic two-step composition it is INCORRECT in general to
multiply standalone DDTs. The theorem below requires an explicit proof
that EVERY exact intermediate-difference fiber has the indicated product
cardinality. The premise is stronger than separate support facts and can
be fulfilled by a problem-specific bijection/fiber-count argument.
-/

namespace Diffan

/-- A local factorization certificate at one selected input/output pair.
    This weaker interface suits *slices* such as the special zero-left
    three-round formulas proved for Magma: it does not demand a formula
    uniformly across every possible differential pair. -/
structure FiberFactorizationAt {X Y Z A B C : Type*}
    [Fintype X] [Fintype B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (c : C) where
  left : B → Nat
  right : B → Nat
  correct : ∀ b,
    intermediateCount sx sy sz f g P Q a b c = left b * right b

/-- An exact product-sum formula for a selected slice follows only
    after the corresponding joint-fiber factorization is certified. -/
theorem composedCount_at_eq_factorized_sum {X Y Z A B C : Type*}
    [Fintype X] [Fintype B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (a : A) (c : C)
    (cert : FiberFactorizationAt sx sy sz f g P Q a c) :
    composedCount sx sz f g P Q a c =
      ∑ b : B, cert.left b * cert.right b := by
  rw [composedCount_eq_sum_intermediate sx sy sz f g P Q a c]
  apply Finset.sum_congr rfl
  intro b _
  exact cert.correct b

/-- Certificate that all *joint* intermediate fibers admit a particular
    two-factor count. Note: `left` and `right` are not presumed to be
    independent marginal DDTs; the `correct` field is essential. -/
structure FiberFactorization {X Y Z A B C : Type*}
    [Fintype X] [Fintype B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop) where
  left : WeightKernel A B
  right : WeightKernel B C
  correct : ∀ a b c,
    intermediateCount sx sy sz f g P Q a b c = left a b * right b c

/-- An exact matrix composition law follows from a proved factorization
    of the real joint trajectory fibers, with no independence axiom. -/
theorem composedCount_eq_kernel_comp {X Y Z A B C : Type*}
    [Fintype X] [Fintype B]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (P : X → Prop) (Q : Y → Prop)
    (cert : FiberFactorization sx sy sz f g P Q)
    (a : A) (c : C) :
    composedCount sx sz f g P Q a c =
      WeightKernel.comp cert.left cert.right a c := by
  rw [composedCount_eq_sum_intermediate sx sy sz f g P Q a c]
  unfold WeightKernel.comp
  apply Finset.sum_congr rfl
  intro b _
  exact cert.correct a b c

/-- In the unconditional case, the same certificate also yields an
    exact formula for the DDT of the composed function. -/
theorem ddt_comp_eq_kernel_comp {X Y Z A B C : Type*}
    [Fintype X] [Fintype B] [DecidableEq C]
    (sx : DifferenceSpace X A) (sy : DifferenceSpace Y B)
    (sz : DifferenceSpace Z C)
    (f : X → Y) (g : Y → Z)
    (cert : FiberFactorization sx sy sz f g
      (fun _ => True) (fun _ => True))
    (a : A) (c : C) :
    ddt sx sz (g ∘ f) a c =
      WeightKernel.comp cert.left cert.right a c := by
  rw [← composedCount_true_eq_ddt sx sz f g a c]
  exact composedCount_eq_kernel_comp sx sy sz f g
    (fun _ => True) (fun _ => True) cert a c

end Diffan
