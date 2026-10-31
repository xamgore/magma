module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundCertifiedFastPath
public import Diffan.TwoRegionCertifiedJoin

@[expose] public section

/-!
# A prioritized two-stage join for a fixed nonzero Magma slice

The first geometric region contains the known true common base: there
is a proof that the two predicted middle points coincide identically
there, so no difference bits need be observed. The second region is the
remaining portion of the 16-base cube, tested by
one difference bit. Outside both regions, full equality is used.

The two regions are selected from the BASE only, with no inspection of
the hidden difference. All window weights are the existing genuine
conditional weights under ONE scheduled master key. This is a semantic
certificate, not a statement about running time; geometric recognition
still has a cost.
-/

namespace Magma.DiffanFiveRoundTwoRegionJoin

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin
open Magma.DiffanFiveRoundGraphSyndrome
open Magma.DiffanFiveRoundNonemptyMaskGain
open Magma.DiffanFiveRoundPrefixKeyFamily
open Magma.DiffanFiveRoundBitCubeExactMask
open Magma.DiffanFiveRoundCertifiedFastPath
open Magma.DiffanFiveRoundTwoBaseExactMask

private abbrev Master :=
  V 256

private abbrev RoundState :=
  V 32 × V 32

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- First priority: the base of the known real five-round path. -/
def provenBase (b : RoundState) : Prop := b = trueMiddle.base

/-- Second priority: the other fifteen vertices of the bit cube. -/
def otherCube (b : RoundState) : Prop :=
  cubeFast b ∧ b ≠ trueMiddle.base

/-- No middle-difference bit is needed on the first region. -/
def zeroBitObservation : Point → Unit := fun _ => ()

/-- A full match is known at the real base for all keys in the family. -/
theorem true_base_graphs_agree (K : Master) (h : sameFirstFive K) :
    reconstructed K chosenInput trueMiddle.base =
      rightReconstructed K chosenOutput trueMiddle.base := by
  rw [reconstructed_eq K h chosenInput trueMiddle.base,
    rightReconstructed_eq K h chosenOutput trueMiddle.base]
  exact true_graphs_agree

/-- Local certificate on the singleton first region. -/
theorem zero_bit_certificate (K : Master) (h : sameFirstFive K)
    (b : RoundState) (hb : provenBase b)
    (_ : zeroBitObservation (reconstructed K chosenInput b) =
      zeroBitObservation (rightReconstructed K chosenOutput b)) :
    reconstructed K chosenInput b =
      rightReconstructed K chosenOutput b := by
  change b = trueMiddle.base at hb
  subst b
  exact true_base_graphs_agree K h

/-- Local certificate on the rest of the cube. -/
theorem one_bit_certificate (K : Master) (h : sameFirstFive K)
    (b : RoundState) (hb : otherCube b)
    (hobs : maskedDifference separatingMask (reconstructed K chosenInput b) =
      maskedDifference separatingMask (rightReconstructed K chosenOutput b)) :
    reconstructed K chosenInput b =
      rightReconstructed K chosenOutput b := by
  exact cube_fast_correct K h b hb.1 hobs

/-- Two local tests, followed by exact equality outside the cube. -/
noncomputable def twoRegionCount (K : Master) (R : Point → Prop) : Nat := by
  classical
  exact Diffan.TwoRegionCertifiedJoin.stagedMass
    provenBase otherCube zeroBitObservation
    (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)

open scoped Classical in
/-- The two-region procedure preserves the full five-round count on
ALL common bases, under any internal predicate R. -/
theorem two_region_exact (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    twoRegionCount K R =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) := by
  classical
  unfold twoRegionCount
  rw [Diffan.TwoRegionCertifiedJoin.staged_eq_exact_of_certificates
    provenBase otherCube zeroBitObservation
    (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)
    (zero_bit_certificate K h) (one_bit_certificate K h)]
  exact (five_exact_as_graph_mass K chosenInput chosenOutput R).symm

open scoped Classical in
/-- Exact budget: each wrongly paired candidate is charged precisely
to its first rejecting stage or to the full fallback. -/
theorem two_region_accounting (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) +
      Diffan.TwoRegionCertifiedJoin.firstRejected provenBase
        zeroBitObservation
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.TwoRegionCertifiedJoin.secondRejected provenBase otherCube
        (maskedDifference separatingMask)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.TwoRegionCertifiedJoin.fallbackRejected provenBase otherCube
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) := by
  classical
  have hc := Diffan.TwoRegionCertifiedJoin.coarse_eq_staged_add_rejections
    provenBase otherCube zeroBitObservation
    (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)
  change (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
    twoRegionCount K R +
      Diffan.TwoRegionCertifiedJoin.firstRejected provenBase
        zeroBitObservation (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.TwoRegionCertifiedJoin.secondRejected provenBase otherCube
        (maskedDifference separatingMask)
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Diffan.TwoRegionCertifiedJoin.fallbackRejected provenBase otherCube
        (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) at hc
  rw [two_region_exact K h R] at hc
  exact hc

/-- The known false join is genuinely handled by stage two. -/
theorem crossed_in_second_region : otherCube crossedBase := by
  refine ⟨crossed_fast, ?_⟩
  intro heq
  have hbad : cubeBase (1 : Fin 16) = cubeBase (0 : Fin 16) := by
    rw [cube_base_one, cube_base_zero]
    exact heq
  have hdistinct : cubeBase (1 : Fin 16) ≠ cubeBase (0 : Fin 16) := by
    decide
  exact hdistinct hbad

open scoped Classical in
/-- The second stage does genuine work with positive conditional mass
on unrestricted five-round trajectories. -/
theorem second_stage_rejection_positive (K : Master) (h : sameFirstFive K) :
    0 < Diffan.TwoRegionCertifiedJoin.secondRejected provenBase otherCube
      (maskedDifference separatingMask)
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  classical
  apply Diffan.TwoRegionCertifiedJoin.second_rejected_pos_of_witness
    provenBase otherCube (maskedDifference separatingMask)
    (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput unrestricted)
    crossedBase
  · rw [baseWeight_eq K h chosenInput chosenOutput unrestricted crossedBase]
    exact crossed_base_weight_positive
  · intro hb
    exact crossed_in_second_region.2 hb
  · exact crossed_in_second_region
  · rw [reconstructed_eq K h chosenInput crossedBase,
        rightReconstructed_eq K h chosenOutput crossedBase]
    exact separating_mask_disagrees

open scoped Classical in
/-- Real paths remain, and the one-bit second stage rejects an active
false join, with no loss and no double counting. -/
theorem exact_nonempty_with_second_stage_gain (K : Master)
    (h : sameFirstFive K) :
    0 < twoRegionCount K unrestricted ∧
    twoRegionCount K unrestricted =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) unrestricted) ∧
    0 < Diffan.TwoRegionCertifiedJoin.secondRejected provenBase otherCube
      (maskedDifference separatingMask)
      (reconstructed K chosenInput) (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  have heq := two_region_exact K h unrestricted
  refine ⟨?_, heq, second_stage_rejection_positive K h⟩
  rw [heq, fiveCount_eq K h
    (inputDifference chosenInput) (outputDifference chosenOutput) unrestricted]
  exact actual_five_round_count_positive

end Magma.DiffanFiveRoundTwoRegionJoin
