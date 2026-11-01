module

import all Init.Data.Range.Basic
public import Magma.Diffan.GCarryFiberTensor
public import Diffan.BlockwiseXorCorrelation

@[expose] public section

/-!
# XOR-correlation of two four-nibble blocks

This is the 16+16 analogue of `Diffan.BlockwiseXorCorrelation`,
using the actual nibble coordinates in the verified Magma carry model.
Both blocks have exactly 16 bits; XOR acts *digitwise*, so there is no
cross-block XOR carry. Arithmetic ADDITION carries remain present in the
four-state mixture indices, not in the XOR shift.
-/

namespace Magma.DiffanGNibbleBlockCorrelation

open Magma.CarryAutomaton
open Magma.DiffanGCarryFiberTensor

/-- XOR shift of four four-bit digits. -/
def halfXor (x y : HalfDigits) : HalfDigits :=
  fun i => xorDigit (x i) (y i)

/-- Two-block XOR shift, with the lower word first. -/
def pairXor (x y : HalfDigits × HalfDigits) : HalfDigits × HalfDigits :=
  (halfXor x.1 y.1, halfXor x.2 y.2)

/-- XOR correlation over a genuine 16-bit coordinate space, encoded
as four independently indexed nibbles. -/
noncomputable def halfCorr (f g : HalfDigits → Nat)
    (h : HalfDigits) : Nat := by
  classical
  exact ∑ x : HalfDigits, f x * g (halfXor x h)

noncomputable def nibbleBlockCorr (f g : (HalfDigits × HalfDigits) → Nat)
    (h : HalfDigits × HalfDigits) : Nat := by
  classical exact ∑ x : HalfDigits × HalfDigits, f x * g (pairXor x h)

/-- Real conditional boundary carries, not independence of halves. -/
noncomputable def nibbleMixture {I : Type*} [Fintype I]
    (lo hi : I → HalfDigits → Nat) :
    (HalfDigits × HalfDigits) → Nat := by
  classical
  exact fun x => ∑ i : I, lo i x.1 * hi i x.2

/-- The correlation of two separated nibble products factors. -/
theorem nibbleBlockCorr_rectangle
    (lo₁ lo₂ hi₁ hi₂ : HalfDigits → Nat)
    (h : HalfDigits × HalfDigits) :
    nibbleBlockCorr (fun x => lo₁ x.1 * hi₁ x.2)
      (fun x => lo₂ x.1 * hi₂ x.2) h =
      halfCorr lo₁ lo₂ h.1 * halfCorr hi₁ hi₂ h.2 := by
  classical
  unfold nibbleBlockCorr pairXor halfCorr
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : HalfDigits, ∑ y : HalfDigits,
        (lo₁ x * hi₁ y) * (lo₂ (halfXor x h.1) * hi₂ (halfXor y h.2))) =
      ∑ x : HalfDigits, ∑ y : HalfDigits,
        (lo₁ x * lo₂ (halfXor x h.1)) *
          (hi₁ y * hi₂ (halfXor y h.2)) := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            ring
    _ = (∑ x : HalfDigits, lo₁ x * lo₂ (halfXor x h.1)) *
          (∑ y : HalfDigits, hi₁ y * hi₂ (halfXor y h.2)) := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- Linearity in the left weight. -/
theorem nibbleBlockCorr_sum_left {I : Type*} [Fintype I]
    (f : I → (HalfDigits × HalfDigits) → Nat)
    (g : (HalfDigits × HalfDigits) → Nat)
    (shift : HalfDigits × HalfDigits) :
    nibbleBlockCorr (fun x => ∑ i : I, f i x) g shift =
      ∑ i : I, nibbleBlockCorr (f i) g shift := by
  classical
  unfold nibbleBlockCorr
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Linearity in the right weight. -/
theorem nibbleBlockCorr_sum_right {I : Type*} [Fintype I]
    (f : (HalfDigits × HalfDigits) → Nat)
    (g : I → (HalfDigits × HalfDigits) → Nat)
    (shift : HalfDigits × HalfDigits) :
    nibbleBlockCorr f (fun x => ∑ i : I, g i x) shift =
      ∑ i : I, nibbleBlockCorr f (g i) shift := by
  classical
  unfold nibbleBlockCorr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Pointwise certificates make full nibble correlation a sum of
products of short correlations. There is no assumption that the carry
state in the two input fibers is the same. -/
theorem nibbleBlockCorr_of_certificates
    {I J : Type*} [Fintype I] [Fintype J]
    (f g : (HalfDigits × HalfDigits) → Nat)
    (l₁ h₁ : I → HalfDigits → Nat)
    (l₂ h₂ : J → HalfDigits → Nat)
    (shift : HalfDigits × HalfDigits)
    (hf : ∀ x, f x = nibbleMixture l₁ h₁ x)
    (hg : ∀ x, g x = nibbleMixture l₂ h₂ x) :
    nibbleBlockCorr f g shift =
      ∑ i : I, ∑ j : J,
        halfCorr (l₁ i) (l₂ j) shift.1 *
          halfCorr (h₁ i) (h₂ j) shift.2 := by
  classical
  have hff : f = nibbleMixture l₁ h₁ := funext hf
  have hgg : g = nibbleMixture l₂ h₂ := funext hg
  rw [hff, hgg]
  calc
    nibbleBlockCorr (nibbleMixture l₁ h₁)
        (nibbleMixture l₂ h₂) shift =
      ∑ i : I, nibbleBlockCorr
        (fun x => l₁ i x.1 * h₁ i x.2)
        (nibbleMixture l₂ h₂) shift := by
          exact nibbleBlockCorr_sum_left
            (fun i x => l₁ i x.1 * h₁ i x.2)
            (nibbleMixture l₂ h₂) shift
    _ = ∑ i : I, ∑ j : J, nibbleBlockCorr
            (fun x => l₁ i x.1 * h₁ i x.2)
            (fun x => l₂ j x.1 * h₂ j x.2) shift := by
          apply Finset.sum_congr rfl
          intro i _
          exact nibbleBlockCorr_sum_right
            (fun x => l₁ i x.1 * h₁ i x.2)
            (fun j x => l₂ j x.1 * h₂ j x.2) shift
    _ = ∑ i : I, ∑ j : J,
          halfCorr (l₁ i) (l₂ j) shift.1 *
            halfCorr (h₁ i) (h₂ j) shift.2 := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact nibbleBlockCorr_rectangle (l₁ i) (l₂ j)
            (h₁ i) (h₂ j) shift

end Magma.DiffanGNibbleBlockCorrelation
