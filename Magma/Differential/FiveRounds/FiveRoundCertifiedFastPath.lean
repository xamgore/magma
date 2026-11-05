module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundBitCubeExactMask
public import Difan.Algorithms.CertifiedFastPath

@[expose] public section

/-!
# A globally exact hybrid join for five Magma rounds

A four-dimensional affine cube provides a certified region where one
bit distinguishes the two reconstructed difference graphs. The join
uses the following checks:

* On the cube, compare only the first middle-difference bit 0x80.
* Outside the cube, compare the two reconstructed full middle points.

This is exact over ALL 64-bit common bases, with NO internal window
restriction, and also for any other internal predicate R. It applies to
every master key in the same-first-five family.
A real false join inside the cube has positive left/right weight and is
already eliminated by the fast one-bit test. Thus the shortcut is used
on an actual candidate, rather than being merely a logical fallback.

The result concerns semantic correctness, not a claim of global speedup:
most bases may require the full comparison, and membership in the small
cube itself has an implementation cost.
-/

namespace Magma.DifanFiveRoundCertifiedFastPath

open Magma
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundZeroBoundaryBaseLabel
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundFixedInputGraphJoin
open Magma.DifanFiveRoundDualBoundaryGraphJoin
open Magma.DifanFiveRoundGraphSyndrome
open Magma.DifanFiveRoundNonemptyMaskGain
open Magma.DifanFiveRoundPrefixKeyFamily
open Magma.DifanFiveRoundBitCubeExactMask

private abbrev Master :=
  V 256

private abbrev RoundState :=
  V 32 × V 32

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- A geometric membership test on the COMMON BASE, independent of
both differences and the reconstructed syndrome. -/
def cubeFast (b : RoundState) : Prop :=
  ∃ i : Fin 16, b = cubeBase i

/-- The finite 16-vertex certificate gives an exact one-bit equality
test whenever the base lies in the geometric cube. -/
theorem cube_fast_correct (K : Master) (h : sameFirstFive K)
    (b : RoundState) (hb : cubeFast b)
    (hobs : maskedDifference separatingMask (reconstructed K chosenInput b) =
      maskedDifference separatingMask (rightReconstructed K chosenOutput b)) :
    reconstructed K chosenInput b =
      rightReconstructed K chosenOutput b := by
  obtain ⟨i, rfl⟩ := hb
  have hp := reconstructed_eq K h chosenInput (cubeBase i)
  have hq := rightReconstructed_eq K h chosenOutput (cubeBase i)
  rw [hp, hq] at hobs ⊢
  rcases cube_full_or_rejected i with heq | hno
  · exact heq
  · exact False.elim (hno hobs)

/-- Piecewise candidate count: one bit on the cube, full equality
outside. The internal restriction is arbitrary and need not constrain
the bases to the cube. -/
noncomputable def adaptiveCandidateMass (K : Master)
    (R : Point → Prop) : Nat := by
  classical
  exact Difan.CertifiedFastPath.hybridMass cubeFast
    (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)

open scoped Classical in
/-- Global semantic exactness: the fast path does not alter the real
five-round count, even if windows explore bases outside the cube. -/
theorem adaptive_exact_for_family (K : Master) (h : sameFirstFive K)
    (R : Point → Prop) :
    adaptiveCandidateMass K R =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) := by
  classical
  unfold adaptiveCandidateMass
  rw [Difan.CertifiedFastPath.hybrid_eq_exact_of_certificate
    cubeFast (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)
    (cube_fast_correct K h)]
  exact (five_exact_as_graph_mass K chosenInput chosenOutput R).symm

open scoped Classical in
/-- Full candidate accounting for the hybrid decision procedure:
all falsely joined mass is rejected either by the one-bit fast path
or by the full comparison off the cube. -/
theorem adaptive_accounting_for_family (K : Master)
    (h : sameFirstFive K) (R : Point → Prop) :
    (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) R) +
      Difan.CertifiedFastPath.fastRejectedMass cubeFast
        (maskedDifference separatingMask)
        (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Difan.CertifiedFastPath.fallbackRejectedMass cubeFast
        (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) := by
  classical
  have hc := Difan.CertifiedFastPath.coarse_eq_hybrid_add_rejections
    cubeFast (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput R)
  change (∑ b : RoundState, baseWeight K chosenInput chosenOutput R b) =
    adaptiveCandidateMass K R +
      Difan.CertifiedFastPath.fastRejectedMass cubeFast
        (maskedDifference separatingMask)
        (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) +
      Difan.CertifiedFastPath.fallbackRejectedMass cubeFast
        (reconstructed K chosenInput)
        (rightReconstructed K chosenOutput)
        (baseWeight K chosenInput chosenOutput R) at hc
  rw [adaptive_exact_for_family K h R] at hc
  exact hc

/-- The known crossed base lies in the fast region and is rejected
without needing a full middle-difference comparison. -/
theorem crossed_fast : cubeFast crossedBase :=
  ⟨1, cube_base_one.symm⟩

open scoped Classical in
/-- The one-bit fast rejection has positive weight even on the FULL
unrestricted five-round support, for every scheduled-key family member. -/
theorem global_fast_rejection_positive (K : Master) (h : sameFirstFive K) :
    0 < Difan.CertifiedFastPath.fastRejectedMass cubeFast
      (maskedDifference separatingMask)
      (reconstructed K chosenInput)
      (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  classical
  apply Difan.CertifiedFastPath.fast_rejected_pos_of_witness
    cubeFast (maskedDifference separatingMask)
    (reconstructed K chosenInput)
    (rightReconstructed K chosenOutput)
    (baseWeight K chosenInput chosenOutput unrestricted)
    crossedBase
  · rw [baseWeight_eq K h chosenInput chosenOutput unrestricted crossedBase]
    exact crossed_base_weight_positive
  · exact crossed_fast
  · rw [reconstructed_eq K h chosenInput crossedBase,
        rightReconstructed_eq K h chosenOutput crossedBase]
    exact separating_mask_disagrees

open scoped Classical in
/-- Global five-round paths survive the hybrid filter, while at least
one false join is removed by the cheap test before fallback. -/
theorem global_nonempty_exact_with_fast_gain (K : Master)
    (h : sameFirstFive K) :
    0 < adaptiveCandidateMass K unrestricted ∧
    adaptiveCandidateMass K unrestricted =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) unrestricted) ∧
    0 < Difan.CertifiedFastPath.fastRejectedMass cubeFast
      (maskedDifference separatingMask)
      (reconstructed K chosenInput)
      (rightReconstructed K chosenOutput)
      (baseWeight K chosenInput chosenOutput unrestricted) := by
  have heq := adaptive_exact_for_family K h unrestricted
  refine ⟨?_, heq, global_fast_rejection_positive K h⟩
  rw [heq, fiveCount_eq K h
    (inputDifference chosenInput) (outputDifference chosenOutput) unrestricted]
  exact actual_five_round_count_positive

end Magma.DifanFiveRoundCertifiedFastPath
