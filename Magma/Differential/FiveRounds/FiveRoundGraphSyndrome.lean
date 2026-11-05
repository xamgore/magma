module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundDualBoundaryGraphJoin
public import Diffan.Fibers.ObservedGraphJoin

@[expose] public section

/-!
# Partially observed mismatch of two reconstructed window graphs

Both boundary differences are fixed. The left and right four-round windows
reconstruct unique full common points from the shared base, using one master
key. A mask on their predicted difference is a sound rejection test; it is
not automatically an exact join certificate.
-/

namespace Magma.DiffanFiveRoundGraphSyndrome

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Observe selected bits of both halves of the middle *difference*. -/
def maskedDifference (mask : RoundState) (p : Point) : RoundState :=
  (p.delta.1 &&& mask.1, p.delta.2 &&& mask.2)

/-- Actual product of left and right window counts at the predictions
from a single common base. Do not confuse with a product of DDTs. -/
noncomputable def baseWeight (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (b : RoundState) : Nat := by
  classical
  exact leftWeight master (inputDifference a) R (reconstructed master a b) *
      rightWeight master (outputDifference outDelta)
        (rightReconstructed master outDelta b)

/-- A mask-based candidate count, before full difference equality. -/
noncomputable def maskCandidateMass (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState) : Nat := by
  classical
  exact Diffan.ObservedGraphJoin.observedMass (maskedDifference mask)
      (reconstructed master a) (rightReconstructed master outDelta)
      (baseWeight master a outDelta R)

/-- False graph joins not noticed by this mask. -/
noncomputable def hiddenMismatchMass (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState) : Nat := by
  classical
  exact Diffan.ObservedGraphJoin.hiddenMass (maskedDifference mask)
      (reconstructed master a) (rightReconstructed master outDelta)
      (baseWeight master a outDelta R)

/-- Candidate pairs demonstrably rejected by inspecting the mask. -/
noncomputable def rejectedMismatchMass (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState) : Nat := by
  classical
  exact Diffan.ObservedGraphJoin.rejectedMass (maskedDifference mask)
      (reconstructed master a) (rightReconstructed master outDelta)
      (baseWeight master a outDelta R)

/-- If the masked predictions differ, no full-point join exists here. -/
theorem mask_disagreement_excludes_join
    (master : Master) (a outDelta b mask : RoundState)
    (h : maskedDifference mask (reconstructed master a b) ≠
      maskedDifference mask (rightReconstructed master outDelta b)) :
    reconstructed master a b ≠ rightReconstructed master outDelta b := by
  intro heq
  exact h (congrArg (maskedDifference mask) heq)

open scoped Classical in
/-- The five-round path count equals the weighted sum over bases
where the two reconstructed full points agree. -/
theorem five_exact_as_graph_mass
    (master : Master) (a outDelta : RoundState) (R : Point → Prop) :
    Fintype.card (FiveRestricted master (inputDifference a)
      (outputDifference outDelta) R) =
      Diffan.ObservedGraphJoin.exactMass
        (reconstructed master a) (rightReconstructed master outDelta)
        (baseWeight master a outDelta R) := by
  classical
  simpa only [Diffan.ObservedGraphJoin.exactMass, baseWeight] using
    five_fixed_boundaries_exact_matching_graphs master a outDelta R

open scoped Classical in
/-- The masked count always overcounts the true five-round mass by
exactly the *hidden* mismatch mass. -/
theorem candidate_eq_five_add_hidden
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState) :
    maskCandidateMass master a outDelta R mask =
      Fintype.card (FiveRestricted master (inputDifference a)
        (outputDifference outDelta) R) +
      hiddenMismatchMass master a outDelta R mask := by
  classical
  unfold maskCandidateMass hiddenMismatchMass
  rw [Diffan.ObservedGraphJoin.observed_eq_exact_add_hidden]
  rw [← five_exact_as_graph_mass master a outDelta R]

open scoped Classical in
/-- Coarse base-only mass splits into exact, hidden, and already
rejected mismatch contributions. -/
theorem coarse_eq_five_add_hidden_add_rejected
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState) :
    (∑ b : RoundState, baseWeight master a outDelta R b) =
      Fintype.card (FiveRestricted master (inputDifference a)
        (outputDifference outDelta) R) +
      hiddenMismatchMass master a outDelta R mask +
      rejectedMismatchMass master a outDelta R mask := by
  classical
  unfold hiddenMismatchMass rejectedMismatchMass
  change Diffan.ObservedGraphJoin.coarseMass
    (baseWeight master a outDelta R) = _
  rw [Diffan.ObservedGraphJoin.coarse_eq_exact_add_hidden_add_rejected
    (maskedDifference mask)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R)]
  rw [← five_exact_as_graph_mass master a outDelta R]

open scoped Classical in
/-- An explicit *support-dependent* certificate for exactness of the
masked candidate count. No claim that a short mask is always exact. -/
theorem candidate_exact_of_active_mask_agreement
    (master : Master) (a outDelta : RoundState)
    (R : Point → Prop) (mask : RoundState)
    (h : ∀ b : RoundState,
      0 < baseWeight master a outDelta R b →
      maskedDifference mask (reconstructed master a b) =
        maskedDifference mask (rightReconstructed master outDelta b) →
      reconstructed master a b = rightReconstructed master outDelta b) :
    maskCandidateMass master a outDelta R mask =
      Fintype.card (FiveRestricted master (inputDifference a)
        (outputDifference outDelta) R) := by
  classical
  unfold maskCandidateMass
  rw [Diffan.ObservedGraphJoin.observed_exact_of_active_agreement
    (maskedDifference mask)
    (reconstructed master a) (rightReconstructed master outDelta)
    (baseWeight master a outDelta R) h]
  rw [← five_exact_as_graph_mass master a outDelta R]

end Magma.DiffanFiveRoundGraphSyndrome
