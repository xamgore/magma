module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundGraphSyndrome
public import Difan.Fibers.ObservedGraphRefinement
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Bit-mask refinement for scheduled five-round graph joins

The same master key determines both reconstructed common points.
Refining a pair of masks is guaranteed not to remove a true join. The
exact new rejection mass is a sum of actual conditional-window products
at the bases where the masks begin to disagree.

Exactness of a mask depends on the active conditional-window support.
-/

namespace Magma.DifanFiveRoundGraphMaskRefinement

open Magma
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundFixedInputGraphJoin
open Magma.DifanFiveRoundDualBoundaryGraphJoin
open Magma.DifanFiveRoundGraphSyndrome

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Each bit observed by `coarse` is also observed by `fine`. -/
def maskIncluded (coarse fine : RoundState) : Prop :=
  coarse.1 &&& fine.1 = coarse.1 ∧
    coarse.2 &&& fine.2 = coarse.2

/-- Bitwise inclusion is enough to preserve any equality already
    established by the finer observation. -/
theorem fine_agreement_implies_coarse
    (coarse fine : RoundState) (hsub : maskIncluded coarse fine)
    (p q : Point)
    (hf : maskedDifference fine p = maskedDifference fine q) :
    maskedDifference coarse p = maskedDifference coarse q := by
  rcases hsub with ⟨h₁, h₂⟩
  have hf₁ := congrArg Prod.fst hf
  have hf₂ := congrArg Prod.snd hf
  change p.delta.1 &&& fine.1 = q.delta.1 &&& fine.1 at hf₁
  change p.delta.2 &&& fine.2 = q.delta.2 &&& fine.2 at hf₂
  change (p.delta.1 &&& coarse.1, p.delta.2 &&& coarse.2) =
    (q.delta.1 &&& coarse.1, q.delta.2 &&& coarse.2)
  apply Prod.ext
  · bv_decide
  · bv_decide

/-- Weight of the false graph pairs eliminated when replacing the
    coarse mask by a finer mask. -/
noncomputable def newlyRejectedMaskMass (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (coarse fine : RoundState) : Nat := by
  classical
  exact Difan.ObservedGraphRefinement.gainedMass
    (maskedDifference coarse) (maskedDifference fine)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R)

open scoped Classical in
/-- Exact improvement identity for two masks of one five-round problem. -/
theorem coarse_candidate_eq_fine_add_gain
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (coarse fine : RoundState)
    (hsub : maskIncluded coarse fine) :
    maskCandidateMass master a outDelta R coarse =
      maskCandidateMass master a outDelta R fine +
        newlyRejectedMaskMass master a outDelta R coarse fine := by
  classical
  exact Difan.ObservedGraphRefinement.observed_eq_refined_add_gain
    (maskedDifference coarse) (maskedDifference fine)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R)
    (fun b hf => fine_agreement_implies_coarse coarse fine hsub _ _ hf)

open scoped Classical in
/-- The same gain is a literal decrease in hidden false joins. -/
theorem coarse_hidden_eq_fine_add_gain
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (coarse fine : RoundState)
    (hsub : maskIncluded coarse fine) :
    hiddenMismatchMass master a outDelta R coarse =
      hiddenMismatchMass master a outDelta R fine +
        newlyRejectedMaskMass master a outDelta R coarse fine := by
  classical
  exact Difan.ObservedGraphRefinement.hidden_eq_refined_add_gain
    (maskedDifference coarse) (maskedDifference fine)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R)
    (fun b hf => fine_agreement_implies_coarse coarse fine hsub _ _ hf)

open scoped Classical in
/-- A witness involving real positive conditional path weights proves
    that refinement gives strict candidate rejection for this slice. -/
theorem fine_mask_strict_of_active_witness
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (coarse fine b : RoundState)
    (hsub : maskIncluded coarse fine)
    (hw : 0 < baseWeight master a outDelta R b)
    (hc : maskedDifference coarse (reconstructed master a b) =
      maskedDifference coarse (rightReconstructed master outDelta b))
    (hf : maskedDifference fine (reconstructed master a b) ≠
      maskedDifference fine (rightReconstructed master outDelta b)) :
    maskCandidateMass master a outDelta R fine <
      maskCandidateMass master a outDelta R coarse := by
  classical
  exact Difan.ObservedGraphRefinement.refined_strict_of_witness
    (maskedDifference coarse) (maskedDifference fine)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R)
    (fun x heq => fine_agreement_implies_coarse coarse fine hsub _ _ heq)
    b hw hc hf

open scoped Classical in
/-- If no positively weighted base is newly separated, adding these
    bits does not change the candidate count. -/
theorem fine_mask_no_gain_of_no_active_witness
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (coarse fine : RoundState)
    (hsub : maskIncluded coarse fine)
    (h : ∀ b : RoundState,
      maskedDifference coarse (reconstructed master a b) =
        maskedDifference coarse (rightReconstructed master outDelta b) →
      maskedDifference fine (reconstructed master a b) ≠
        maskedDifference fine (rightReconstructed master outDelta b) →
      baseWeight master a outDelta R b = 0) :
    maskCandidateMass master a outDelta R coarse =
      maskCandidateMass master a outDelta R fine := by
  classical
  have hz : newlyRejectedMaskMass master a outDelta R coarse fine = 0 := by
    unfold newlyRejectedMaskMass Difan.ObservedGraphRefinement.gainedMass
    apply Finset.sum_eq_zero
    intro b _
    by_cases hc : maskedDifference coarse (reconstructed master a b) =
        maskedDifference coarse (rightReconstructed master outDelta b)
    · by_cases hf : maskedDifference fine (reconstructed master a b) ≠
          maskedDifference fine (rightReconstructed master outDelta b)
      · simp [hc, hf, h b hc hf]
      · simp [hc, hf]
    · simp [hc]
  rw [coarse_candidate_eq_fine_add_gain master a outDelta R coarse fine hsub, hz]
  omega

end Magma.DifanFiveRoundGraphMaskRefinement
