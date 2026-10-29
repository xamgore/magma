module

public import Diffan.WeightedKernel
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.MatrixBridge — natural-weight kernels as matrices

Purely mathematical interface, with no reference to Magma.
`WeightKernel.comp` is ordinary finite matrix multiplication.
This theorem identifies the operation; it does NOT assert that an arbitrary
weighted kernel counts the trajectories of a particular program.
-/

namespace Diffan

/-- View a natural-weighted relation as a matrix. -/
def WeightKernel.toMatrix {A B : Type*}
    (w : WeightKernel A B) : Matrix A B Nat :=
  Matrix.of w

/-- The general convolution and finite matrix multiplication coincide. -/
theorem WeightKernel.toMatrix_comp {A B C : Type*} [Fintype B]
    (p : WeightKernel A B) (q : WeightKernel B C) :
    WeightKernel.toMatrix (WeightKernel.comp p q) =
      WeightKernel.toMatrix p * WeightKernel.toMatrix q := by
  ext a c
  change (∑ b : B, p a b * q b c) =
    ((Matrix.of p) * (Matrix.of q)) a c
  rw [Matrix.mul_apply]
  rfl

end Diffan
