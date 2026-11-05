module

import all Init.Data.Range.Basic
public import Mathlib

@[expose] public section

/-!
# Exact XOR correlation from small independent blocks

Natural-number weights on an XOR product space admit correlation
identities that also account for multiplicities beyond Boolean predicates.

If two word-weight functions have *certified separable decompositions*
indexed by small interface types I and J, then the full correlation is a
sum over I × J of products of small-word correlations. Crucially no
independence is postulated: any carry or other coupling must be encoded
by the indices and proved in the pointwise decomposition hypotheses.

The results are algebraic statements about finite sums, not a verified
FWHT implementation or an unconditional decomposition of Magma fibers.
-/

namespace Difan.BlockwiseXorCorrelation

/-- Weighted XOR correlation on an n-bit word. -/
noncomputable def wordCorr {n : Nat}
    (f g : BitVec n → Nat) (h : BitVec n) : Nat := by
  classical
  exact ∑ x : BitVec n, f x * g (x ^^^ h)

/-- Weighted XOR correlation on a pair of blocks. The shift acts
componentwise and therefore does not propagate carries between blocks. -/
noncomputable def blockCorr {n m : Nat}
    (f g : (BitVec n × BitVec m) → Nat)
    (h : BitVec n × BitVec m) : Nat := by
  classical
  exact ∑ x : BitVec n × BitVec m,
    f x * g (x.1 ^^^ h.1, x.2 ^^^ h.2)

/-- A separable weight (rank-one tensor) on two bit blocks. -/
def rectangle {n m : Nat}
    (f : BitVec n → Nat) (g : BitVec m → Nat) :
    (BitVec n × BitVec m) → Nat :=
  fun x => f x.1 * g x.2

/-- The correlation of two rectangular weights factors into the product
of their two smaller correlations. -/
theorem blockCorr_rectangle {n m : Nat}
    (f p : BitVec n → Nat) (g q : BitVec m → Nat)
    (h₁ : BitVec n) (h₂ : BitVec m) :
    blockCorr (rectangle f g) (rectangle p q) (h₁, h₂) =
      wordCorr f p h₁ * wordCorr g q h₂ := by
  classical
  unfold blockCorr rectangle wordCorr
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : BitVec n, ∑ y : BitVec m,
        (f x * g y) * (p (x ^^^ h₁) * q (y ^^^ h₂))) =
      ∑ x : BitVec n, ∑ y : BitVec m,
        (f x * p (x ^^^ h₁)) * (g y * q (y ^^^ h₂)) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = (∑ x : BitVec n, f x * p (x ^^^ h₁)) *
          (∑ y : BitVec m, g y * q (y ^^^ h₂)) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Exact linearity in the left weight of a block correlation. -/
theorem blockCorr_sum_left {n m : Nat} {I : Type*} [Fintype I]
    (f : I → (BitVec n × BitVec m) → Nat)
    (g : (BitVec n × BitVec m) → Nat)
    (h : BitVec n × BitVec m) :
    blockCorr (fun x => ∑ i : I, f i x) g h =
      ∑ i : I, blockCorr (f i) g h := by
  classical
  unfold blockCorr
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Exact linearity in the right weight of a block correlation. -/
theorem blockCorr_sum_right {n m : Nat} {I : Type*} [Fintype I]
    (f : (BitVec n × BitVec m) → Nat)
    (g : I → (BitVec n × BitVec m) → Nat)
    (h : BitVec n × BitVec m) :
    blockCorr f (fun x => ∑ i : I, g i x) h =
      ∑ i : I, blockCorr f (g i) h := by
  classical
  unfold blockCorr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A weight represented as a sum of separable block weights.
The index represents a certified interface state (for example, a
boundary carry). No disjointness is assumed; multiplicities are retained.
-/
noncomputable def mixture {n m : Nat} {I : Type*} [Fintype I]
    (low : I → BitVec n → Nat)
    (high : I → BitVec m → Nat) :
    (BitVec n × BitVec m) → Nat := by
  classical
  exact fun x => ∑ i : I, rectangle (low i) (high i) x

/-- Main tensorization theorem. If both full-word weights are sums
of products of local weights indexed by interface conditions, their
32-bit (or arbitrary-bit) XOR correlation is computed by a sum of
products of smaller-word correlations. -/
theorem blockCorr_mixture {n m : Nat}
    {I J : Type*} [Fintype I] [Fintype J]
    (leftLow : I → BitVec n → Nat)
    (leftHigh : I → BitVec m → Nat)
    (rightLow : J → BitVec n → Nat)
    (rightHigh : J → BitVec m → Nat)
    (h₁ : BitVec n) (h₂ : BitVec m) :
    blockCorr (mixture leftLow leftHigh)
        (mixture rightLow rightHigh) (h₁, h₂) =
      ∑ i : I, ∑ j : J,
        wordCorr (leftLow i) (rightLow j) h₁ *
          wordCorr (leftHigh i) (rightHigh j) h₂ := by
  classical
  calc
    blockCorr (mixture leftLow leftHigh)
        (mixture rightLow rightHigh) (h₁, h₂) =
      ∑ i : I, blockCorr (rectangle (leftLow i) (leftHigh i))
        (mixture rightLow rightHigh) (h₁, h₂) := by
          exact blockCorr_sum_left
            (fun i => rectangle (leftLow i) (leftHigh i))
            (mixture rightLow rightHigh) (h₁, h₂)
    _ = ∑ i : I, ∑ j : J,
          blockCorr (rectangle (leftLow i) (leftHigh i))
            (rectangle (rightLow j) (rightHigh j)) (h₁, h₂) := by
          apply Finset.sum_congr rfl
          intro i _
          exact blockCorr_sum_right
            (rectangle (leftLow i) (leftHigh i))
            (fun j => rectangle (rightLow j) (rightHigh j)) (h₁, h₂)
    _ = ∑ i : I, ∑ j : J,
          wordCorr (leftLow i) (rightLow j) h₁ *
            wordCorr (leftHigh i) (rightHigh j) h₂ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact blockCorr_rectangle (leftLow i) (rightLow j)
            (leftHigh i) (rightHigh j) h₁ h₂

/-- A certified pointwise decomposition of *arbitrary* weights is enough.
This is the interface to a future carry-DP theorem for actual Magma
indicator fibers. -/
theorem blockCorr_of_certified_decompositions {n m : Nat}
    {I J : Type*} [Fintype I] [Fintype J]
    (f g : (BitVec n × BitVec m) → Nat)
    (leftLow : I → BitVec n → Nat)
    (leftHigh : I → BitVec m → Nat)
    (rightLow : J → BitVec n → Nat)
    (rightHigh : J → BitVec m → Nat)
    (h₁ : BitVec n) (h₂ : BitVec m)
    (hf : ∀ x, f x = mixture leftLow leftHigh x)
    (hg : ∀ x, g x = mixture rightLow rightHigh x) :
    blockCorr f g (h₁, h₂) =
      ∑ i : I, ∑ j : J,
        wordCorr (leftLow i) (rightLow j) h₁ *
          wordCorr (leftHigh i) (rightHigh j) h₂ := by
  have hfl : f = mixture leftLow leftHigh := funext hf
  have hgr : g = mixture rightLow rightHigh := funext hg
  rw [hfl, hgr]
  exact blockCorr_mixture leftLow leftHigh rightLow rightHigh h₁ h₂

end Difan.BlockwiseXorCorrelation
