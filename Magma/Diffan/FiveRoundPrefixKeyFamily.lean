module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundNonemptyMaskGain

@[expose] public section

/-!
# Five-round witness and mask-gain transport across master keys

A five-round ordinary-G prefix depends only on scheduled round keys 0..4.
Fixing those five subkeys to the values at `chosenMaster` transfers BOTH
certificates in `FiveRoundNonemptyMaskGain`: a real five-round path with the
same nonzero endpoint differences and a strictly positive one-bit rejection.

This is a condition on ONE 256-bit master key, not on independently selected
keys for overlapping windows. The remaining master-key words are not read
by this five-round prefix.
-/

namespace Magma.DiffanFiveRoundPrefixKeyFamily

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin
open Magma.DiffanFiveRoundGraphSyndrome
open Magma.DiffanFiveRoundGraphMaskRefinement
open Magma.DiffanFiveRoundNonemptyMaskGain

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- The five ACTUAL scheduled subkeys used by five ordinary rounds are
identical to those of the zero-master witness. -/
def sameFirstFive (K : Master) : Prop :=
  roundKey K (0 : Fin 32) = roundKey chosenMaster (0 : Fin 32) ∧
  roundKey K (1 : Fin 32) = roundKey chosenMaster (1 : Fin 32) ∧
  roundKey K (2 : Fin 32) = roundKey chosenMaster (2 : Fin 32) ∧
  roundKey K (3 : Fin 32) = roundKey chosenMaster (3 : Fin 32) ∧
  roundKey K (4 : Fin 32) = roundKey chosenMaster (4 : Fin 32)

theorem chosenMaster_mem : sameFirstFive chosenMaster :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Agreement of all five scheduled keys identifies the restricted
trajectory types for arbitrary endpoint and middle conditions. -/
theorem fiveRestricted_type_eq (K : Master) (h : sameFirstFive K)
    (P Q R : Point → Prop) :
    FiveRestricted K P Q R = FiveRestricted chosenMaster P Q R := by
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  unfold FiveRestricted ScheduledFive
  rw [h₀, h₁, h₂, h₃, h₄]

/-- Restricted left-window types coincide, at EACH fixed full midpoint. -/
theorem leftAt_type_eq (K : Master) (h : sameFirstFive K)
    (P R : Point → Prop) (m : Point) :
    LeftAt K P R m = LeftAt chosenMaster P R m := by
  rcases h with ⟨h₀, h₁, h₂, h₃, _⟩
  unfold LeftAt LeftEligible
  rw [h₀, h₁, h₂, h₃]

/-- Restricted right-window types coincide, at EACH fixed full midpoint. -/
theorem rightAt_type_eq (K : Master) (h : sameFirstFive K)
    (Q : Point → Prop) (m : Point) :
    RightAt K Q m = RightAt chosenMaster Q m := by
  rcases h with ⟨_, h₁, h₂, h₃, h₄⟩
  unfold RightAt RightEligible
  rw [h₁, h₂, h₃, h₄]

open scoped Classical in
/-- In particular, all conditional left weights at fixed points agree. -/
theorem leftWeight_eq (K : Master) (h : sameFirstFive K)
    (P R : Point → Prop) (m : Point) :
    leftWeight K P R m = leftWeight chosenMaster P R m := by
  classical
  change Fintype.card (LeftAt K P R m) =
    Fintype.card (LeftAt chosenMaster P R m)
  exact Fintype.card_congr (Equiv.cast (leftAt_type_eq K h P R m))

open scoped Classical in
/-- And all conditional right weights at fixed points agree. -/
theorem rightWeight_eq (K : Master) (h : sameFirstFive K)
    (Q : Point → Prop) (m : Point) :
    rightWeight K Q m = rightWeight chosenMaster Q m := by
  classical
  change Fintype.card (RightAt K Q m) =
    Fintype.card (RightAt chosenMaster Q m)
  exact Fintype.card_congr (Equiv.cast (rightAt_type_eq K h Q m))

/-- The left graph needs just the first scheduled subkey. -/
theorem reconstructed_eq (K : Master) (h : sameFirstFive K)
    (a b : RoundState) :
    reconstructed K a b = reconstructed chosenMaster a b := by
  have h₀ := h.1
  unfold reconstructed predictedDelta
  rw [h₀]

/-- The right graph uses precisely scheduled subkeys 1..4. -/
theorem rightReconstructed_eq (K : Master) (h : sameFirstFive K)
    (z b : RoundState) :
    rightReconstructed K z b = rightReconstructed chosenMaster z b := by
  rcases h with ⟨_, h₁, h₂, h₃, h₄⟩
  unfold rightReconstructed rightPredictedDelta rightBaseTrack rightFrom
  simp only [h₁, h₂, h₃, h₄]

open scoped Classical in
/-- The products of the real conditional weights are also unchanged. -/
theorem baseWeight_eq (K : Master) (h : sameFirstFive K)
    (a z : RoundState) (R : Point → Prop) (b : RoundState) :
    baseWeight K a z R b = baseWeight chosenMaster a z R b := by
  classical
  unfold baseWeight
  rw [reconstructed_eq K h a b, rightReconstructed_eq K h z b]
  rw [leftWeight_eq K h, rightWeight_eq K h]

open scoped Classical in
/-- Agreement of the scheduled keys preserves the entire mask-refinement gain.
The mask and both endpoint differences do NOT change with the master. -/
theorem gain_eq (K : Master) (h : sameFirstFive K)
    (a z : RoundState) (R : Point → Prop)
    (coarse fine : RoundState) :
    newlyRejectedMaskMass K a z R coarse fine =
      newlyRejectedMaskMass chosenMaster a z R coarse fine := by
  classical
  have hp : reconstructed K a = reconstructed chosenMaster a := by
    funext b
    exact reconstructed_eq K h a b
  have hq : rightReconstructed K z = rightReconstructed chosenMaster z := by
    funext b
    exact rightReconstructed_eq K h z b
  have hw : baseWeight K a z R = baseWeight chosenMaster a z R := by
    funext b
    exact baseWeight_eq K h a z R b
  unfold newlyRejectedMaskMass
  rw [hp, hq, hw]

open scoped Classical in
/-- Transport of the original exact five-round count. -/
theorem fiveCount_eq (K : Master) (h : sameFirstFive K)
    (P Q R : Point → Prop) :
    Fintype.card (FiveRestricted K P Q R) =
      Fintype.card (FiveRestricted chosenMaster P Q R) := by
  classical
  exact Fintype.card_congr (Equiv.cast (fiveRestricted_type_eq K h P Q R))

open scoped Classical in
/-- A single, fixed nonzero input/output differential has BOTH genuine
paths and strictly useful one-bit rejection for EVERY master in this family. -/
theorem nonempty_and_gain_for_family (K : Master) (h : sameFirstFive K) :
    0 < Fintype.card (FiveRestricted K
      (inputDifference chosenInput)
      (outputDifference chosenOutput) unrestricted) ∧
    0 < newlyRejectedMaskMass K chosenInput chosenOutput unrestricted
      emptyMask separatingMask := by
  classical
  constructor
  · rw [fiveCount_eq K h]
    exact actual_five_round_count_positive
  · rw [gain_eq K h]
    exact nonempty_slice_gain_positive

/-- The family contains the original key and at least one other genuine
256-bit key. Bit 0 is in a master-key word NOT used by rounds 0..4. -/
def alternateMaster : Master := (1#256)

theorem alternateMaster_mem : sameFirstFive alternateMaster := by
  unfold sameFirstFive alternateMaster chosenMaster
  decide

theorem alternateMaster_ne : alternateMaster ≠ chosenMaster := by decide

/-- Thus the family is nontrivial without postulating independent round keys. -/
theorem family_nontrivial :
    ∃ K : Master, K ≠ chosenMaster ∧ sameFirstFive K :=
  ⟨alternateMaster, alternateMaster_ne, alternateMaster_mem⟩

end Magma.DiffanFiveRoundPrefixKeyFamily
