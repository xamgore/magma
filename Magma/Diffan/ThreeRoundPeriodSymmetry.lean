module

import all Init.Data.Range.Basic
public import Magma.Diffan.ThreeRoundConditionalSlices

@[expose] public section

/-!
# Period symmetry of actual three-round conditional fibers

A 32-bit XOR derivative is invariant under translation by its own input
difference. This creates a *shared* translation symmetry between the
first-round derivative (input difference `aR`) and the last-round
derivative (input difference `bL`).

If the two derivatives admit the same XOR period `h`, the conditional
Z-fibers are exactly equal at R and R XOR h.  In particular, when
`aR = bL`, the period h = aR always exists.  This is a two-point
(or orbitwise) symmetry, NOT full uniformity over all R of the same c.
-/

namespace Magma.DiffanThreeRoundPeriodSymmetry

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanThreeRoundRightHistogram
open Magma.DiffanThreeRoundConditionalSlices

private abbrev Word :=
  V 32

/-- Every XOR derivative is periodic under its input difference.
    This uses no particular property of Magma's nonlinear function. -/
theorem gDifference_xor_period (k x d : Word) :
    gDifference k (xor x d) d = gDifference k x d := by
  unfold gDifference
  change (g k ((x ^^^ d) ^^^ d)) ^^^ (g k (x ^^^ d)) =
    (g k (x ^^^ d)) ^^^ (g k x)
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using
    (BitVec.xor_comm (g k x) (g k (x ^^^ d)))

/-- An XOR period of the first derivative preserves its c-label. -/
theorem intermediateDifference_translate
    (k₀ aL aR h R : Word)
    (h₀ : ∀ x : Word,
      gDifference k₀ (xor x h) aR = gDifference k₀ x aR) :
    intermediateDifference k₀ aL aR (xor R h) =
      intermediateDifference k₀ aL aR R := by
  simp only [intermediateDifference, h₀ R]

/-- The middle test depends on R only through its first-round c-label. -/
theorem middleCondition_translate
    (k₀ k₁ aL aR bL h R Z : Word)
    (h₀ : ∀ x : Word,
      gDifference k₀ (xor x h) aR = gDifference k₀ x aR) :
    middleCondition k₀ k₁ aL aR bL (xor R h, Z) ↔
      middleCondition k₀ k₁ aL aR bL (R, Z) := by
  have hc := intermediateDifference_translate k₀ aL aR h R h₀
  simp only [middleCondition, hc]

/-- If the third derivative also has period h, the actual final
    right-output label is unchanged by R -> R XOR h. -/
theorem rightOutput_translate
    (k₀ k₁ k₂ aL aR bL h R Z : Word)
    (h₀ : ∀ x : Word,
      gDifference k₀ (xor x h) aR = gDifference k₀ x aR)
    (h₂ : ∀ x : Word,
      gDifference k₂ (xor x h) bL = gDifference k₂ x bL) :
    rightOutput k₀ k₁ k₂ aL aR bL (xor R h, Z) =
      rightOutput k₀ k₁ k₂ aL aR bL (R, Z) := by
  have hc := intermediateDifference_translate k₀ aL aR h R h₀
  have hx : xor (g k₁ Z) (xor R h) =
      xor (xor (g k₁ Z) R) h := by
    change (g k₁ Z ^^^ (R ^^^ h)) = ((g k₁ Z ^^^ R) ^^^ h)
    exact (BitVec.xor_assoc (g k₁ Z) R h).symm
  unfold rightOutput
  rw [hc, hx, h₂ (xor (g k₁ Z) R)]

/-- A common XOR period preserves the entire conditional Z-fiber cardinality,
    not merely the underlying intermediate difference. -/
theorem conditionalZCount_translate
    (k₀ k₁ k₂ aL aR bL bR h R : Word)
    (h₀ : ∀ x : Word,
      gDifference k₀ (xor x h) aR = gDifference k₀ x aR)
    (h₂ : ∀ x : Word,
      gDifference k₂ (xor x h) bL = gDifference k₂ x bL) :
    conditionalZCount k₀ k₁ k₂ aL aR bL bR (xor R h) =
      conditionalZCount k₀ k₁ k₂ aL aR bL bR R := by
  classical
  unfold conditionalZCount Diffan.FiberUniformity.conditionalCount
  simp only
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro Z _
  have hm := middleCondition_translate k₀ k₁ aL aR bL h R Z h₀
  have hr := rightOutput_translate k₀ k₁ k₂ aL aR bL h R Z h₀ h₂
  simp only [hm, hr]

/-- Canonical nontrivial candidate: whenever bL=aR=d, both derivatives
    share the period h=d (even though the keys k₀ and k₂ differ). -/
theorem conditionalZCount_diagonal_period
    (k₀ k₁ k₂ aL d bR R : Word) :
    conditionalZCount k₀ k₁ k₂ aL d d bR (xor R d) =
      conditionalZCount k₀ k₁ k₂ aL d d bR R := by
  exact conditionalZCount_translate k₀ k₁ k₂ aL d d bR d R
    (fun x => gDifference_xor_period k₀ x d)
    (fun x => gDifference_xor_period k₂ x d)

/-- Each first-round class c also contains the paired R XOR d. -/
theorem intermediateDifference_diagonal_period
    (k₀ aL d R : Word) :
    intermediateDifference k₀ aL d (xor R d) =
      intermediateDifference k₀ aL d R := by
  exact intermediateDifference_translate k₀ aL d d R
    (fun x => gDifference_xor_period k₀ x d)

/-- Hence the actual summand in our proved c-slice decomposition is
    invariant under R -> R XOR d when aR=bL=d.  This is useful for
    quotienting individual c-fibers, but does *not* establish that all
    different R within a c-fiber have equal weights. -/
theorem diagonal_slice_summand_period
    (k₀ k₁ k₂ aL d bR c R : Word) :
    (if intermediateDifference k₀ aL d (xor R d) = c then
      conditionalZCount k₀ k₁ k₂ aL d d bR (xor R d)
    else 0) =
    (if intermediateDifference k₀ aL d R = c then
      conditionalZCount k₀ k₁ k₂ aL d d bR R
    else 0) := by
  rw [intermediateDifference_diagonal_period,
    conditionalZCount_diagonal_period]

end Magma.DiffanThreeRoundPeriodSymmetry
