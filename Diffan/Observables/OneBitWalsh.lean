module

import all Init.Data.Range.Basic
public import Mathlib

@[expose] public section

/-!
# One-bit Walsh-Hadamard butterfly and XOR convolution

A small, elementary, kernel-checkable algebraic base case for a future
recursively verified XOR-convolution algorithm. In particular the
transform needs signed intermediate values; it is defined over Int,
not Nat. No claim is made about a 32-bit array implementation.
-/

namespace Diffan.OneBitWalsh

/-- One Walsh-Hadamard butterfly on a Boolean-indexed signal. -/
def butterfly (f : Bool → Int) : Bool → Int :=
  fun b => if b then f false - f true else f false + f true

/-- XOR convolution of two one-bit signals. -/
def xorConvolution (f g : Bool → Int) : Bool → Int :=
  fun b => if b then
    f false * g true + f true * g false
  else
    f false * g false + f true * g true

/-- Applying the unnormalized butterfly twice multiplies by 2. -/
theorem butterfly_twice (f : Bool → Int) (b : Bool) :
    butterfly (butterfly f) b = 2 * f b := by
  cases b <;> simp [butterfly] <;> ring

/-- One-bit XOR convolution becomes pointwise multiplication in the
Walsh basis. This is the basic arithmetic step of FWHT. -/
theorem butterfly_convolution (f g : Bool → Int) (b : Bool) :
    butterfly (xorConvolution f g) b =
      butterfly f b * butterfly g b := by
  cases b <;> simp [butterfly, xorConvolution] <;> ring

/-- The one-bit inverse formula, expressed without division. -/
theorem xorConvolution_recovery (f g : Bool → Int) (b : Bool) :
    2 * xorConvolution f g b =
      butterfly
        (fun t => butterfly f t * butterfly g t) b := by
  have hspec : butterfly (xorConvolution f g) =
      (fun t => butterfly f t * butterfly g t) := by
    funext t
    exact butterfly_convolution f g t
  calc
    2 * xorConvolution f g b =
        butterfly (butterfly (xorConvolution f g)) b :=
          (butterfly_twice (xorConvolution f g) b).symm
    _ = butterfly (fun t => butterfly f t * butterfly g t) b :=
          congrArg (fun v : Bool → Int => butterfly v b) hspec

end Diffan.OneBitWalsh
