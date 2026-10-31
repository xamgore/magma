module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundGraphMaskRefinement
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Strict one-bit rejection for real overlapping Magma windows

For EVERY 256-bit master key, construct a left four-round window with
fixed nonzero input difference and a right four-round window with the
same first-common base but a different first-common difference.

The right output boundary is defined by its real execution, so the two
conditional weights are positive with an unrestricted middle point. Both boundary differences are nonzero.
A one-bit mask provably rejects the false join, whereas the zero mask
accepts it. No claim that this particular output difference is key-
independent, or that the exact five-round fiber is nonempty, is made.
-/

namespace Magma.DiffanFiveRoundConcreteMaskGain

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin
open Magma.DiffanFiveRoundGraphSyndrome
open Magma.DiffanFiveRoundGraphMaskRefinement

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- A fixed, nonzero input difference, independent of the master key. -/
def inputDir : RoundState := ((0#32), (1#32))

/-- Explicit starting point of the real left window. -/
def startPoint : Point := ⟨((0#32), (0#32)), inputDir⟩

/-- Actual first common point of the left four-round window. -/
def leftMiddle (master : Master) : Point :=
  (leftFrom master startPoint).p₁

/-- The crossed right point has exactly the same base. Only bit 1 of
its first difference word is toggled. -/
def rightMiddle (master : Master) : Point :=
  ⟨(leftMiddle master).base,
    ((leftMiddle master).delta.1 ^^^ (2#32),
      (leftMiddle master).delta.2)⟩

/-- A genuine *fixed* output difference for the chosen master, obtained
by executing a real right window. This may depend on the master. -/
def outputDir (master : Master) : RoundState :=
  (rightFrom master (rightMiddle master)).p₄.delta

/-- The common base used to compare the two reconstructed graphs. -/
def commonBase (master : Master) : RoundState := (leftMiddle master).base

/-- Zero bits of the difference are inspected by the coarse mask. -/
def coarseMask : RoundState := ((0#32), (0#32))

/-- Only bit 1 of the first difference word is inspected by the fine mask. -/
def fineMask : RoundState := ((2#32), (0#32))

theorem masks_included : maskIncluded coarseMask fineMask := by
  unfold maskIncluded coarseMask fineMask
  decide

/-- First Feistel difference coordinate after round 0 equals the
second input difference coordinate, regardless of key. -/
theorem leftMiddle_first_delta (master : Master) :
    (leftMiddle master).delta.1 = (1#32) := by
  have h := congrArg Prod.fst
    (left_first_difference master inputDir (leftFrom master startPoint) rfl)
  simpa only [leftMiddle, predictedDelta, inputDir] using h

/-- A nonzero right starting difference ensures a nonzero output
boundary, by reversibility of the four actual right rounds. -/
theorem outputDir_nonzero (master : Master) :
    outputDir master ≠ zeroDifference := by
  have hn : (rightMiddle master).delta ≠ zeroDifference := by
    intro heq
    have h := congrArg Prod.fst heq
    change (leftMiddle master).delta.1 ^^^ (2#32) = (0#32) at h
    rw [leftMiddle_first_delta master] at h
    have hh : ((1#32) ^^^ (2#32)) ≠ (0#32) := by decide
    exact hh h
  intro hz
  have hfirst :
      (rightFrom master (rightMiddle master)).p₀.delta = zeroDifference :=
    right_first_zero (rightFrom master (rightMiddle master)) hz
  exact hn hfirst

open scoped Classical in
/-- The left conditional window weight is positive at this real point. -/
theorem left_weight_positive (master : Master) :
    0 < leftWeight master (inputDifference inputDir) unrestricted
      (leftMiddle master) := by
  classical
  change 0 < Fintype.card
    (LeftAt master (inputDifference inputDir) unrestricted (leftMiddle master))
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom master startPoint, ⟨rfl, trivial⟩⟩, rfl⟩⟩

open scoped Classical in
/-- The right conditional window weight is positive: the chosen right
window reaches precisely its own declared output difference. -/
theorem right_weight_positive (master : Master) :
    0 < rightWeight master (outputDifference (outputDir master))
      (rightMiddle master) := by
  classical
  change 0 < Fintype.card
    (RightAt master (outputDifference (outputDir master)) (rightMiddle master))
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨rightFrom master (rightMiddle master), rfl⟩, rfl⟩⟩

/-- The two graph predictions really are the two explicit real
middle points, with the same base. -/
theorem left_prediction_eq (master : Master) :
    reconstructed master inputDir (commonBase master) = leftMiddle master := by
  exact (left_active_graph master inputDir unrestricted
    (leftMiddle master) (left_weight_positive master)).symm

theorem right_prediction_eq (master : Master) :
    rightReconstructed master (outputDir master) (commonBase master) = rightMiddle master := by
  have h :=
    (right_active_output_graph master (outputDir master) (rightMiddle master)
        (right_weight_positive master)).symm
  exact h

open scoped Classical in
/-- This actual cross-pair has strictly positive product weight at
its common base, using one real master key on both sides. -/
theorem active_base (master : Master) :
    0 < baseWeight master inputDir (outputDir master) unrestricted
      (commonBase master) := by
  classical
  change 0 < leftWeight master (inputDifference inputDir) unrestricted
      (reconstructed master inputDir (commonBase master)) *
    rightWeight master (outputDifference (outputDir master))
      (rightReconstructed master (outputDir master) (commonBase master))
  rw [left_prediction_eq master, right_prediction_eq master]
  exact Nat.mul_pos (left_weight_positive master) (right_weight_positive master)

/-- The coarse mask accepts the pair simply because it observes nothing. -/
theorem coarse_agreement (master : Master) :
    maskedDifference coarseMask (reconstructed master inputDir (commonBase master)) =
      maskedDifference coarseMask
        (rightReconstructed master (outputDir master) (commonBase master)) := by
  simp only [maskedDifference, coarseMask, BitVec.and_zero]

/-- The fine mask detects bit 1, which differs in the two real middle
points, independently of all S-box outputs and all subkeys. -/
theorem fine_disagreement (master : Master) :
    maskedDifference fineMask (reconstructed master inputDir (commonBase master)) ≠
      maskedDifference fineMask
        (rightReconstructed master (outputDir master) (commonBase master)) := by
  rw [left_prediction_eq master, right_prediction_eq master]
  intro heq
  have hf := congrArg Prod.fst heq
  change (leftMiddle master).delta.1 &&& (2#32) =
    ((leftMiddle master).delta.1 ^^^ (2#32)) &&& (2#32) at hf
  have hbit : ∀ x : Word,
      x &&& (2#32) ≠ (x ^^^ (2#32)) &&& (2#32) := by
    intro x
    bv_decide
  exact hbit _ hf

open scoped Classical in
/-- A one-bit refinement strictly reduces the actual candidate mass.
The output boundary is nonzero and is defined by a genuine right window. -/
theorem actual_one_bit_strict_gain (master : Master) :
    maskCandidateMass master inputDir (outputDir master) unrestricted fineMask <
      maskCandidateMass master inputDir (outputDir master) unrestricted coarseMask := by
  classical
  exact fine_mask_strict_of_active_witness master inputDir (outputDir master)
    unrestricted coarseMask fineMask (commonBase master)
    masks_included (active_base master) (coarse_agreement master)
    (fine_disagreement master)

open scoped Classical in
/-- The mass removed by this one-bit refinement is strictly positive. -/
theorem gained_mass_positive (master : Master) :
    0 < newlyRejectedMaskMass master inputDir (outputDir master)
      unrestricted coarseMask fineMask := by
  classical
  exact Diffan.ObservedGraphRefinement.gained_pos_of_witness
    (maskedDifference coarseMask) (maskedDifference fineMask)
    (reconstructed master inputDir)
    (rightReconstructed master (outputDir master))
    (baseWeight master inputDir (outputDir master) unrestricted)
    (commonBase master) (active_base master)
    (coarse_agreement master) (fine_disagreement master)

end Magma.DiffanFiveRoundConcreteMaskGain
