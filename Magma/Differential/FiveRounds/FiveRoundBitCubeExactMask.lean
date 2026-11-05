module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundTwoBaseExactMask
public import Difan.Fibers.IndexedSupportExactness

@[expose] public section

/-!
# A 16-base bit cube with an exact ONE-BIT five-round graph join

A predicate on the second intermediate state selects a 4-bit
affine cube of first-common bases (16 possibilities). The four free bits
of the SECOND 32-bit base word are 0, 3, 8, and 14, while the first base
word is zero. The cube contains both the real five-round path and the
crossed false graph join.

For the fixed nonzero endpoint differences of `FiveRoundNonemptyMaskGain`,
an explicit, small finite bit computation certifies that every nonzero
cube offset is rejected by bit 0x80 of the FIRST middle-difference word.
The zero offset has fully matching graph predictions because it comes
from a real five-round trajectory. This gives exactness on 16 bases,
with positive exact path mass and positive rejection gain, for every
master key with the same five initial scheduled subkeys.

This is a bit-cube restriction, not a claim of global one-bit exactness.
The predicate is imposed on the ACTUAL p₂ state of the left window; it
never inspects the reconstructed graph equality or its syndrome.
-/

namespace Magma.DifanFiveRoundBitCubeExactMask

open Magma
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundLabelJoinDefect
open Magma.DifanFourRoundForcedMiddleDifference
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundZeroBoundaryBaseLabel
open Magma.DifanFiveRoundFixedInputGraphJoin
open Magma.DifanFiveRoundDualBoundaryGraphJoin
open Magma.DifanFiveRoundGraphSyndrome
open Magma.DifanFiveRoundGraphMaskRefinement
open Magma.DifanFiveRoundNonemptyMaskGain
open Magma.DifanFiveRoundPrefixKeyFamily
open Magma.DifanFiveRoundTwoBaseExactMask

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Embed the four bits of a 4-bit index in positions 0,3,8,14 of a
32-bit base word. These positions are fixed independently of the graph
mismatch and define a standard 4-dimensional affine Boolean cube. -/
def cubeOffset (i : Fin 16) : Word :=
  (if i.val % 2 = 1 then (1#32) else (0#32)) ^^^
  (if (i.val / 2) % 2 = 1 then (8#32) else (0#32)) ^^^
  (if (i.val / 4) % 2 = 1 then (256#32) else (0#32)) ^^^
  (if (i.val / 8) % 2 = 1 then (16384#32) else (0#32))

/-- The sixteen possible bases of the common point after round 1. -/
def cubeBase (i : Fin 16) : RoundState :=
  ((0#32), trueMiddle.base.2 ^^^ cubeOffset i)

theorem cube_base_zero : cubeBase (0 : Fin 16) = trueMiddle.base := by decide

theorem cube_base_one : cubeBase (1 : Fin 16) = crossedBase := by decide

/-- The restriction is imposed on the real second state `p₂` in the
five-round fiber. Its base must be a round-G image of this bit cube.
It does NOT require agreement of either reconstructed difference. -/
def cubeSecondSelected (p : Point) : Prop :=
  ∃ i : Fin 16,
    p.base = G (roundKey chosenMaster (1 : Fin 32)) (cubeBase i)

theorem true_second_in_cube : cubeSecondSelected (leftFrom chosenMaster trueStart).p₂ := by
  refine ⟨0, ?_⟩
  change
    G (roundKey chosenMaster (1 : Fin 32)) trueMiddle.base =
      G (roundKey chosenMaster (1 : Fin 32)) (cubeBase 0)
  rw [cube_base_zero]

theorem crossed_second_in_cube : cubeSecondSelected (leftFrom chosenMaster crossedStart).p₂ := by
  refine ⟨1, ?_⟩
  change
    G (roundKey chosenMaster (1 : Fin 32)) crossedLeftMiddle.base =
      G (roundKey chosenMaster (1 : Fin 32)) (cubeBase 1)
  rw [crossed_left_base, cube_base_one]

open scoped Classical in
/-- Positively weighted common bases must belong to the 16-element
cube, by eligibility of the left window and injectivity of Feistel G. -/
theorem active_base_in_cube (b : RoundState)
    (h : 0 < baseWeight chosenMaster chosenInput chosenOutput
      cubeSecondSelected b) :
    ∃ i : Fin 16, b = cubeBase i := by
  classical
  have hleft : 0 < leftWeight chosenMaster (inputDifference chosenInput)
      cubeSecondSelected (reconstructed chosenMaster chosenInput b) := by
    change 0 < leftWeight chosenMaster (inputDifference chosenInput)
      cubeSecondSelected (reconstructed chosenMaster chosenInput b) *
      rightWeight chosenMaster (outputDifference chosenOutput)
        (rightReconstructed chosenMaster chosenOutput b) at h
    exact pos_of_mul_pos_left h (Nat.zero_le _)
  change 0 < Fintype.card (LeftAt chosenMaster (inputDifference chosenInput)
    cubeSecondSelected (reconstructed chosenMaster chosenInput b)) at hleft
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hleft
  obtain ⟨i, hselected⟩ : cubeSecondSelected w.1.1.p₂ := w.1.2.2
  have hcommon : w.1.1.p₁ = reconstructed chosenMaster chosenInput b := w.2
  have hbase : w.1.1.p₂.base =
      G (roundKey chosenMaster (1 : Fin 32)) b := by
    calc
      w.1.1.p₂.base = (step (roundKey chosenMaster (1 : Fin 32))
          w.1.1.p₁).base :=
        congrArg (fun p : Point => p.base) w.1.1.h₁.symm
      _ = G (roundKey chosenMaster (1 : Fin 32)) w.1.1.p₁.base := rfl
      _ = G (roundKey chosenMaster (1 : Fin 32)) b := by
        rw [hcommon]
        rfl
  exact ⟨i, (GEquiv (roundKey chosenMaster (1 : Fin 32))).injective
    (hbase.symm.trans hselected)⟩

/-- All fifteen nonzero cube offsets disagree in the observed bit.
The zero offset corresponds to the genuine five-round path. -/
theorem cube_bit_certificate (i : Fin 16) :
    i = 0 ∨
      maskedDifference separatingMask
        (reconstructed chosenMaster chosenInput (cubeBase i)) ≠
      maskedDifference separatingMask
        (rightReconstructed chosenMaster chosenOutput (cubeBase i)) := by
  revert i
  decide +kernel

/-- Turn a short bitwise certificate into full compatibility-or-reject
on every indexed base of the bit cube. -/
theorem cube_full_or_rejected (i : Fin 16) :
    reconstructed chosenMaster chosenInput (cubeBase i) =
      rightReconstructed chosenMaster chosenOutput (cubeBase i) ∨
    maskedDifference separatingMask
      (reconstructed chosenMaster chosenInput (cubeBase i)) ≠
    maskedDifference separatingMask
      (rightReconstructed chosenMaster chosenOutput (cubeBase i)) := by
  rcases cube_bit_certificate i with hi | hbad
  · left
    rw [hi, cube_base_zero]
    exact true_graphs_agree
  · right
    exact hbad

open scoped Classical in
/-- Exact one-bit counting on a STRUCTURED 16-base support. -/
theorem cube_one_bit_exact :
    maskCandidateMass chosenMaster chosenInput chosenOutput
      cubeSecondSelected separatingMask =
    Fintype.card (FiveRestricted chosenMaster
      (inputDifference chosenInput) (outputDifference chosenOutput)
      cubeSecondSelected) := by
  classical
  change Difan.ObservedGraphJoin.observedMass
    (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput cubeSecondSelected) = _
  rw [Difan.IndexedSupportExactness.observed_exact_of_indexed_support
    (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput cubeSecondSelected)
    cubeBase active_base_in_cube cube_full_or_rejected]
  exact (five_exact_as_graph_mass chosenMaster chosenInput chosenOutput
    cubeSecondSelected).symm

/-- The genuine five-round path survives the 16-base restriction. -/
def cubeTrueJoined : FiveRestricted chosenMaster
    (inputDifference chosenInput) (outputDifference chosenOutput)
    cubeSecondSelected :=
  (fiveMiddleSigmaEquiv chosenMaster
    (inputDifference chosenInput)
    (outputDifference chosenOutput) cubeSecondSelected).symm
    ⟨trueMiddle,
      (⟨⟨leftFrom chosenMaster trueStart, ⟨rfl, true_second_in_cube⟩⟩, rfl⟩,
       ⟨⟨rightFrom chosenMaster trueMiddle, true_right_output⟩, rfl⟩)⟩

open scoped Classical in
theorem cube_true_positive :
    0 <
      Fintype.card
        (FiveRestricted chosenMaster (inputDifference chosenInput) (outputDifference chosenOutput)
          cubeSecondSelected) := by
  classical exact Fintype.card_pos_iff.mpr ⟨cubeTrueJoined⟩

open scoped Classical in
theorem crossed_cube_left_positive :
    0 <
      leftWeight chosenMaster (inputDifference chosenInput) cubeSecondSelected
        crossedLeftMiddle := by
  classical
  change
    0 <
      Fintype.card
        (LeftAt chosenMaster (inputDifference chosenInput) cubeSecondSelected crossedLeftMiddle)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom chosenMaster crossedStart, ⟨rfl, crossed_second_in_cube⟩⟩, rfl⟩⟩

open scoped Classical in
theorem crossed_cube_weight_positive :
    0 < baseWeight chosenMaster chosenInput chosenOutput cubeSecondSelected crossedBase := by
  classical
  change
    0 <
      leftWeight chosenMaster (inputDifference chosenInput) cubeSecondSelected
          (reconstructed chosenMaster chosenInput crossedBase) *
        rightWeight chosenMaster (outputDifference chosenOutput)
          (rightReconstructed chosenMaster chosenOutput crossedBase)
  rw [crossed_left_prediction]
  exact Nat.mul_pos crossed_cube_left_positive crossed_right_weight_positive

open scoped Classical in
/-- The short mask is useful as well as exact: one of the 16 bases
has real positive left/right weights but is rejected by its single bit. -/
theorem cube_gain_positive :
    0 < newlyRejectedMaskMass chosenMaster chosenInput chosenOutput
      cubeSecondSelected emptyMask separatingMask := by
  classical
  exact Difan.ObservedGraphRefinement.gained_pos_of_witness
    (maskedDifference emptyMask) (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput cubeSecondSelected)
    crossedBase crossed_cube_weight_positive
    empty_mask_agrees separating_mask_disagrees

open scoped Classical in
/-- A general transport law for any restriction R: the five scheduled
subkeys, not the other 96 master-key bits, determine the masked mass. -/
theorem cube_mask_transport (K : Master) (h : sameFirstFive K) :
    maskCandidateMass K chosenInput chosenOutput cubeSecondSelected
        separatingMask =
      maskCandidateMass chosenMaster chosenInput chosenOutput
        cubeSecondSelected separatingMask := by
  classical
  have hp : reconstructed K chosenInput =
      reconstructed chosenMaster chosenInput := by
    funext b
    exact reconstructed_eq K h chosenInput b
  have hq : rightReconstructed K chosenOutput =
      rightReconstructed chosenMaster chosenOutput := by
    funext b
    exact rightReconstructed_eq K h chosenOutput b
  have hw : baseWeight K chosenInput chosenOutput cubeSecondSelected =
      baseWeight chosenMaster chosenInput chosenOutput cubeSecondSelected := by
    funext b
    exact baseWeight_eq K h chosenInput chosenOutput cubeSecondSelected b
  unfold maskCandidateMass
  rw [hp, hq, hw]

open scoped Classical in
/-- Sixteen bases, one bit, a genuine nonzero five-round slice,
zero hidden false joins and a strictly positive rejected mass, uniformly
across the nontrivial five-subkey master-key family. -/
theorem sixteen_base_exact_for_family (K : Master) (h : sameFirstFive K) :
    0 < Fintype.card (FiveRestricted K
      (inputDifference chosenInput) (outputDifference chosenOutput)
      cubeSecondSelected) ∧
    maskCandidateMass K chosenInput chosenOutput cubeSecondSelected
        separatingMask =
      Fintype.card (FiveRestricted K
        (inputDifference chosenInput) (outputDifference chosenOutput)
        cubeSecondSelected) ∧
    hiddenMismatchMass K chosenInput chosenOutput
        cubeSecondSelected separatingMask = 0 ∧
    0 < newlyRejectedMaskMass K chosenInput chosenOutput
        cubeSecondSelected emptyMask separatingMask := by
  classical
  have hfive := fiveCount_eq K h
    (inputDifference chosenInput) (outputDifference chosenOutput)
    cubeSecondSelected
  have hmask := cube_mask_transport K h
  have hgain := gain_eq K h chosenInput chosenOutput
    cubeSecondSelected emptyMask separatingMask
  have hexact : maskCandidateMass K chosenInput chosenOutput
      cubeSecondSelected separatingMask =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) cubeSecondSelected) := by
    rw [hmask, hfive]
    exact cube_one_bit_exact
  have hzero : hiddenMismatchMass K chosenInput chosenOutput
      cubeSecondSelected separatingMask = 0 := by
    have heq := candidate_eq_five_add_hidden K chosenInput chosenOutput
      cubeSecondSelected separatingMask
    rw [hexact] at heq
    omega
  refine ⟨?_, hexact, hzero, ?_⟩
  · rw [hfive]
    exact cube_true_positive
  · rw [hgain]
    exact cube_gain_positive

open scoped Classical in
/-- The empty mask misses a genuinely positive contribution on the
same larger support, for every master key in the family. -/
theorem cube_zero_bit_hidden_positive_for_family
    (K : Master) (h : sameFirstFive K) :
    0 < hiddenMismatchMass K chosenInput chosenOutput
      cubeSecondSelected emptyMask := by
  classical
  have hx := sixteen_base_exact_for_family K h
  have hd := coarse_hidden_eq_fine_add_gain K chosenInput chosenOutput
    cubeSecondSelected emptyMask separatingMask masks_ordered
  rw [hx.2.2.1] at hd
  omega

end Magma.DifanFiveRoundBitCubeExactMask
