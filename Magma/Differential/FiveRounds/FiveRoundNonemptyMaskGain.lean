module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundConcreteMaskGain

@[expose] public section

/-!
# A nonempty five-round differential with a strictly useful mask

Fix the zero 256-bit master key.  Both endpoint differences are explicit and
nonzero.  The same endpoint slice contains a genuine five-round path
AND a positively weighted false join at a different common base.

The numerical checks involve only constant executions of five ordinary
Magma rounds and one four-round backwards difference reconstruction.
-/

namespace Magma.DifanFiveRoundNonemptyMaskGain

open Magma
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundLabelJoinDefect
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundZeroBoundaryBaseLabel
open Magma.DifanFiveRoundFixedInputGraphJoin
open Magma.DifanFiveRoundDualBoundaryGraphJoin
open Magma.DifanFiveRoundGraphSyndrome
open Magma.DifanFiveRoundGraphMaskRefinement
open Magma.DifanFiveRoundConcreteMaskGain

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- A single *explicit* genuine Magma master key. -/
def chosenMaster : Master := (0#256)

/-- Fixed, nonzero input direction. -/
def chosenInput : RoundState := ((0#32), (1#32))

/-- Fixed, nonzero output direction, independent of the runtime master. -/
def chosenOutput : RoundState :=
  ((0x05808401 : Word), (0x04485036 : Word))

/-- The witness starts at the zero base and has chosen input difference. -/
def trueStart : Point :=
  ⟨((0#32), (0#32)), chosenInput⟩

def trueMiddle : Point :=
  (leftFrom chosenMaster trueStart).p₁

/-- Execution of the genuine right four-round window reaches the
specified output difference.  This is a small closed calculation. -/
theorem true_right_output :
    (rightFrom chosenMaster trueMiddle).p₄.delta = chosenOutput := by
  decide +kernel

/-- An actual five-round path with both prescribed endpoint differences. -/
def trueJoined : FiveRestricted chosenMaster
    (inputDifference chosenInput) (outputDifference chosenOutput) unrestricted :=
  (fiveMiddleSigmaEquiv chosenMaster
    (inputDifference chosenInput)
    (outputDifference chosenOutput) unrestricted).symm
    ⟨trueMiddle,
      (⟨⟨leftFrom chosenMaster trueStart, ⟨rfl, trivial⟩⟩, rfl⟩,
       ⟨⟨rightFrom chosenMaster trueMiddle, true_right_output⟩, rfl⟩)⟩

open scoped Classical in
/-- This five-round slice has positive EXACT path mass. -/
theorem actual_five_round_count_positive :
    0 < Fintype.card (FiveRestricted chosenMaster
      (inputDifference chosenInput)
      (outputDifference chosenOutput) unrestricted) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨trueJoined⟩

/-- The second left window has the SAME difference at its input,
with a distinct base state at its first common point. -/
def crossedStart : Point :=
  ⟨((1#32), (0#32)), chosenInput⟩

def crossedLeftMiddle : Point :=
  (leftFrom chosenMaster crossedStart).p₁

/-- At the common point, changing the first input-base word from 0 to 1
changes the second common base word by exactly one bit. -/
def crossedBase : RoundState :=
  ((0#32), (0xbe5b60c3 : Word))

theorem crossed_left_base : crossedLeftMiddle.base = crossedBase := by decide

open scoped Classical in
/-- Actual left path: positive conditional mass at its common point. -/
theorem crossed_left_weight_positive :
    0 < leftWeight chosenMaster (inputDifference chosenInput)
      unrestricted crossedLeftMiddle := by
  classical
  change 0 < Fintype.card
    (LeftAt chosenMaster (inputDifference chosenInput)
      unrestricted crossedLeftMiddle)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom chosenMaster crossedStart,
    ⟨rfl, trivial⟩⟩, rfl⟩⟩

/-- The left graph prediction equals the actual crossed left point. -/
theorem crossed_left_prediction :
    reconstructed chosenMaster chosenInput crossedBase =
      crossedLeftMiddle := by
  have h := (left_active_graph chosenMaster chosenInput
    unrestricted crossedLeftMiddle crossed_left_weight_positive).symm
  change reconstructed chosenMaster chosenInput crossedLeftMiddle.base =
    crossedLeftMiddle at h
  rw [crossed_left_base] at h
  exact h

/-- The right graph reconstructed from the SAME prescribed output
difference indeed executes to that output.  Only four constant rounds
are checked. -/
theorem crossed_right_output :
    (rightFrom chosenMaster
      (rightReconstructed chosenMaster chosenOutput crossedBase)).p₄.delta =
      chosenOutput := by
  decide +kernel

open scoped Classical in
/-- Thus the crossed right window is independently genuine and active. -/
theorem crossed_right_weight_positive :
    0 < rightWeight chosenMaster (outputDifference chosenOutput)
      (rightReconstructed chosenMaster chosenOutput crossedBase) := by
  classical
  change 0 < Fintype.card
    (RightAt chosenMaster (outputDifference chosenOutput)
      (rightReconstructed chosenMaster chosenOutput crossedBase))
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨rightFrom chosenMaster
    (rightReconstructed chosenMaster chosenOutput crossedBase),
    crossed_right_output⟩, rfl⟩⟩

/-- The first common difference word predicted backwards from the
right is different from the left's prediction. -/
theorem crossed_right_first_difference :
    (rightReconstructed chosenMaster chosenOutput crossedBase).delta.1 =
      (0x00850581 : Word) := by
  decide +kernel

/-- One bit in the first middle difference word detects the crossed
pair. -/
def emptyMask : RoundState := ((0#32), (0#32))

def separatingMask : RoundState :=
  ((128#32), (0#32))

theorem masks_ordered : maskIncluded emptyMask separatingMask := by
  unfold maskIncluded emptyMask separatingMask
  decide

open scoped Classical in
/-- The two genuine windows are active at the same base, although their
full middle differences disagree. -/
theorem crossed_base_weight_positive :
    0 < baseWeight chosenMaster chosenInput chosenOutput
      unrestricted crossedBase := by
  classical
  change 0 < leftWeight chosenMaster (inputDifference chosenInput)
      unrestricted (reconstructed chosenMaster chosenInput crossedBase) *
    rightWeight chosenMaster (outputDifference chosenOutput)
      (rightReconstructed chosenMaster chosenOutput crossedBase)
  rw [crossed_left_prediction]
  exact Nat.mul_pos crossed_left_weight_positive crossed_right_weight_positive

/-- The zero mask accepts every pair. -/
theorem empty_mask_agrees :
    maskedDifference emptyMask
      (reconstructed chosenMaster chosenInput crossedBase) =
    maskedDifference emptyMask
      (rightReconstructed chosenMaster chosenOutput crossedBase) := by
  simp [maskedDifference, emptyMask]

/-- The one-bit mask separates the two independently real windows. -/
theorem separating_mask_disagrees :
    maskedDifference separatingMask
      (reconstructed chosenMaster chosenInput crossedBase) ≠
    maskedDifference separatingMask
      (rightReconstructed chosenMaster chosenOutput crossedBase) := by
  intro heq
  have h := congrArg Prod.fst heq
  change
    (reconstructed chosenMaster chosenInput crossedBase).delta.1 &&& (128#32) =
      (rightReconstructed chosenMaster chosenOutput crossedBase).delta.1 &&& (128#32) at h
  have hleft :
      (reconstructed chosenMaster chosenInput crossedBase).delta.1 = (1#32) := rfl
  rw [hleft, crossed_right_first_difference] at h
  have hneq : ((1#32) &&& (128#32)) ≠
      ((0x00850581 : Word) &&& (128#32)) := by decide
  exact hneq h

open scoped Classical in
/-- A useful refinement in a slice already containing a true path. -/
theorem nonempty_slice_strict_mask_gain :
    maskCandidateMass chosenMaster chosenInput chosenOutput unrestricted
        separatingMask <
      maskCandidateMass chosenMaster chosenInput chosenOutput unrestricted
        emptyMask := by
  classical
  exact fine_mask_strict_of_active_witness chosenMaster chosenInput
    chosenOutput unrestricted emptyMask separatingMask crossedBase
    masks_ordered crossed_base_weight_positive empty_mask_agrees
    separating_mask_disagrees

open scoped Classical in
/-- The gain itself is strictly positive, for the same fixed boundaries. -/
theorem nonempty_slice_gain_positive :
    0 < newlyRejectedMaskMass chosenMaster chosenInput chosenOutput
      unrestricted emptyMask separatingMask := by
  classical
  exact Difan.ObservedGraphRefinement.gained_pos_of_witness
    (maskedDifference emptyMask) (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput unrestricted)
    crossedBase crossed_base_weight_positive empty_mask_agrees
    separating_mask_disagrees

open scoped Classical in
/-- A genuine five-round path and strictly positive bit-mask refinement
gain coexist under one fixed key and one fixed
(nonzero) input/output differential. -/
theorem nonempty_and_strict_gain :
    0 < Fintype.card (FiveRestricted chosenMaster
      (inputDifference chosenInput)
      (outputDifference chosenOutput) unrestricted) ∧
    0 < newlyRejectedMaskMass chosenMaster chosenInput chosenOutput
      unrestricted emptyMask separatingMask := by
  exact ⟨actual_five_round_count_positive, nonempty_slice_gain_positive⟩

end Magma.DifanFiveRoundNonemptyMaskGain
