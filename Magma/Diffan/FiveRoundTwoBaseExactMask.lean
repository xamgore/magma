module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundPrefixKeyFamily
public import Diffan.TwoBaseSupportExactness

@[expose] public section

/-!
# A genuine one-bit exact graph join on an explicitly restricted Magma fiber

Fix the same nonzero input/output differences as in
`FiveRoundNonemptyMaskGain`. Restrict the *actual second-round middle
point*, the location of predicate `R` in `FiveRestricted`, to the
one-round images of two concrete first-common bases.

Because an ordinary Feistel round is bijective on base states, there
are then at most two bases with positive conditional product weights.
One base has a genuine compatible path. At the other, the same real
left and right windows disagree in bit 0x80 of the first middle
difference word. Thus the one-bit mask is exact on this nonempty
restricted fiber, while a zero-bit test strictly overcounts.

The two-base restriction is intentionally explicit. This is a positive
support-dependent certificate, NOT global one-bit sufficiency on all
2^64 common bases. The certificates transfer to every master with
identical first five scheduled round keys.
-/

namespace Magma.DiffanFiveRoundTwoBaseExactMask

open Magma
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundDualBoundaryGraphJoin
open Magma.DiffanFiveRoundGraphSyndrome
open Magma.DiffanFiveRoundGraphMaskRefinement
open Magma.DiffanFiveRoundNonemptyMaskGain
open Magma.DiffanFiveRoundPrefixKeyFamily

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- A genuine predicate on the SECOND point of the left window, not
an external truncation of a finite sum. Its two allowed base states
are actual round-1 images of the true and crossed first-common bases. -/
def selectedSecondBase (p : Point) : Prop :=
  p.base = G (roundKey chosenMaster (1 : Fin 32)) trueMiddle.base ∨
  p.base = G (roundKey chosenMaster (1 : Fin 32)) crossedBase

theorem true_second_selected : selectedSecondBase (leftFrom chosenMaster trueStart).p₂ := by
  left
  change
    G (roundKey chosenMaster (1 : Fin 32)) trueMiddle.base =
      G (roundKey chosenMaster (1 : Fin 32)) trueMiddle.base
  rfl

theorem crossed_second_selected : selectedSecondBase (leftFrom chosenMaster crossedStart).p₂ := by
  right
  change
    G (roundKey chosenMaster (1 : Fin 32)) crossedLeftMiddle.base =
      G (roundKey chosenMaster (1 : Fin 32)) crossedBase
  rw [crossed_left_base]

/-- The actual five-round execution survives the middle restriction. -/
def selectedTrueJoined : FiveRestricted chosenMaster
    (inputDifference chosenInput) (outputDifference chosenOutput)
    selectedSecondBase :=
  (fiveMiddleSigmaEquiv chosenMaster
    (inputDifference chosenInput)
    (outputDifference chosenOutput) selectedSecondBase).symm
    ⟨trueMiddle,
      (⟨⟨leftFrom chosenMaster trueStart, ⟨rfl, true_second_selected⟩⟩, rfl⟩,
       ⟨⟨rightFrom chosenMaster trueMiddle, true_right_output⟩, rfl⟩)⟩

open scoped Classical in
theorem selected_five_positive :
    0 <
      Fintype.card
        (FiveRestricted chosenMaster (inputDifference chosenInput) (outputDifference chosenOutput)
          selectedSecondBase) := by
  classical exact Fintype.card_pos_iff.mpr ⟨selectedTrueJoined⟩

open scoped Classical in
theorem true_left_selected_positive :
    0 < leftWeight chosenMaster (inputDifference chosenInput) selectedSecondBase trueMiddle := by
  classical
  change
    0 <
      Fintype.card (LeftAt chosenMaster (inputDifference chosenInput) selectedSecondBase trueMiddle)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom chosenMaster trueStart, ⟨rfl, true_second_selected⟩⟩, rfl⟩⟩

open scoped Classical in
theorem true_right_positive :
    0 < rightWeight chosenMaster (outputDifference chosenOutput) trueMiddle := by
  classical
  change 0 < Fintype.card (RightAt chosenMaster (outputDifference chosenOutput) trueMiddle)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨rightFrom chosenMaster trueMiddle, true_right_output⟩, rfl⟩⟩

/-- The actual five-round path forces the two predictions to coincide
at its common base. -/
theorem true_graphs_agree :
    reconstructed chosenMaster chosenInput trueMiddle.base =
      rightReconstructed chosenMaster chosenOutput trueMiddle.base := by
  have hl := (left_active_graph chosenMaster chosenInput
    selectedSecondBase trueMiddle true_left_selected_positive).symm
  have hr := right_active_output_graph chosenMaster chosenOutput
    trueMiddle true_right_positive
  exact hl.trans hr

open scoped Classical in
theorem crossed_left_selected_positive :
    0 <
      leftWeight chosenMaster (inputDifference chosenInput) selectedSecondBase
        crossedLeftMiddle := by
  classical
  change
    0 <
      Fintype.card
        (LeftAt chosenMaster (inputDifference chosenInput) selectedSecondBase crossedLeftMiddle)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom chosenMaster crossedStart, ⟨rfl, crossed_second_selected⟩⟩, rfl⟩⟩

open scoped Classical in
/-- The crossed base retains independently valid windows and a
positive weight even after the actual interior predicate is imposed. -/
theorem crossed_selected_base_weight_positive :
    0 < baseWeight chosenMaster chosenInput chosenOutput
      selectedSecondBase crossedBase := by
  classical
  change 0 < leftWeight chosenMaster (inputDifference chosenInput)
      selectedSecondBase (reconstructed chosenMaster chosenInput crossedBase) *
    rightWeight chosenMaster (outputDifference chosenOutput)
      (rightReconstructed chosenMaster chosenOutput crossedBase)
  rw [crossed_left_prediction]
  exact Nat.mul_pos crossed_left_selected_positive crossed_right_weight_positive

open scoped Classical in
/-- A positive left conditional weight carries a real second-point
witness, whose base is the round-1 image of the first common base. -/
theorem active_base_is_one_of_two (b : RoundState)
    (h : 0 < baseWeight chosenMaster chosenInput chosenOutput
      selectedSecondBase b) :
    b = trueMiddle.base ∨ b = crossedBase := by
  classical
  have hleft : 0 < leftWeight chosenMaster (inputDifference chosenInput)
      selectedSecondBase (reconstructed chosenMaster chosenInput b) := by
    change 0 < leftWeight chosenMaster (inputDifference chosenInput)
      selectedSecondBase (reconstructed chosenMaster chosenInput b) *
      rightWeight chosenMaster (outputDifference chosenOutput)
        (rightReconstructed chosenMaster chosenOutput b) at h
    exact pos_of_mul_pos_left h (Nat.zero_le _)
  change 0 < Fintype.card (LeftAt chosenMaster (inputDifference chosenInput)
    selectedSecondBase (reconstructed chosenMaster chosenInput b)) at hleft
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hleft
  have hselected : selectedSecondBase w.1.1.p₂ := w.1.2.2
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
  rcases hselected with hgood | hbad
  · left
    exact (GEquiv (roundKey chosenMaster (1 : Fin 32))).injective
      (hbase.symm.trans hgood)
  · right
    exact (GEquiv (roundKey chosenMaster (1 : Fin 32))).injective
      (hbase.symm.trans hbad)

open scoped Classical in
/-- ONE bit of the middle difference is sufficient on the actual
selected support; at the genuine base there is full equality, and at
the crossed base the bit already disagrees. -/
theorem one_bit_exact_selected :
    maskCandidateMass chosenMaster chosenInput chosenOutput
      selectedSecondBase separatingMask =
    Fintype.card (FiveRestricted chosenMaster
      (inputDifference chosenInput) (outputDifference chosenOutput)
      selectedSecondBase) := by
  classical
  change Diffan.ObservedGraphJoin.observedMass
    (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput selectedSecondBase) = _
  rw [Diffan.TwoBaseSupportExactness.observed_exact_of_two_base_support
    (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput selectedSecondBase)
    trueMiddle.base crossedBase active_base_is_one_of_two
    true_graphs_agree separating_mask_disagrees]
  exact (five_exact_as_graph_mass chosenMaster chosenInput chosenOutput
    selectedSecondBase).symm

open scoped Classical in
theorem one_bit_hidden_zero_selected :
    hiddenMismatchMass chosenMaster chosenInput chosenOutput selectedSecondBase separatingMask =
      0 := by
  classical
  have heq :=
    candidate_eq_five_add_hidden chosenMaster chosenInput chosenOutput selectedSecondBase
      separatingMask
  rw [one_bit_exact_selected] at heq
  omega

open scoped Classical in
/-- The bit is not vacuous: an independently valid crossed pair has
positive weight but is rejected by this one-bit observation. -/
theorem selected_gain_positive :
    0 < newlyRejectedMaskMass chosenMaster chosenInput chosenOutput
      selectedSecondBase emptyMask separatingMask := by
  classical
  exact Diffan.ObservedGraphRefinement.gained_pos_of_witness
    (maskedDifference emptyMask) (maskedDifference separatingMask)
    (reconstructed chosenMaster chosenInput)
    (rightReconstructed chosenMaster chosenOutput)
    (baseWeight chosenMaster chosenInput chosenOutput selectedSecondBase)
    crossedBase crossed_selected_base_weight_positive
    empty_mask_agrees separating_mask_disagrees

open scoped Classical in
/-- Equality of five scheduled subkeys transports the entire masked
candidate mass, including all actual conditional weights. -/
theorem selected_mask_mass_transport (K : Master) (h : sameFirstFive K) :
    maskCandidateMass K chosenInput chosenOutput selectedSecondBase
        separatingMask =
      maskCandidateMass chosenMaster chosenInput chosenOutput
        selectedSecondBase separatingMask := by
  classical
  have hp : reconstructed K chosenInput =
      reconstructed chosenMaster chosenInput := by
    funext b
    exact reconstructed_eq K h chosenInput b
  have hq : rightReconstructed K chosenOutput =
      rightReconstructed chosenMaster chosenOutput := by
    funext b
    exact rightReconstructed_eq K h chosenOutput b
  have hw : baseWeight K chosenInput chosenOutput selectedSecondBase =
      baseWeight chosenMaster chosenInput chosenOutput selectedSecondBase := by
    funext b
    exact baseWeight_eq K h chosenInput chosenOutput selectedSecondBase b
  unfold maskCandidateMass
  rw [hp, hq, hw]

open scoped Classical in
/-- A nonzero fixed endpoint slice has a genuine
five-round path, and a strictly positive mask gain, yet *zero* hidden
mismatch mass for a one-bit label, across a nontrivial key family. -/
theorem exact_one_bit_for_family (K : Master) (h : sameFirstFive K) :
    0 < Fintype.card (FiveRestricted K
      (inputDifference chosenInput) (outputDifference chosenOutput)
      selectedSecondBase) ∧
    maskCandidateMass K chosenInput chosenOutput selectedSecondBase
        separatingMask =
      Fintype.card (FiveRestricted K
        (inputDifference chosenInput) (outputDifference chosenOutput)
        selectedSecondBase) ∧
    hiddenMismatchMass K chosenInput chosenOutput selectedSecondBase
        separatingMask = 0 ∧
    0 < newlyRejectedMaskMass K chosenInput chosenOutput
        selectedSecondBase emptyMask separatingMask := by
  classical
  have hfive := fiveCount_eq K h
    (inputDifference chosenInput) (outputDifference chosenOutput)
    selectedSecondBase
  have hmask := selected_mask_mass_transport K h
  have hgain := gain_eq K h chosenInput chosenOutput
    selectedSecondBase emptyMask separatingMask
  have hexact : maskCandidateMass K chosenInput chosenOutput
      selectedSecondBase separatingMask =
      Fintype.card (FiveRestricted K (inputDifference chosenInput)
        (outputDifference chosenOutput) selectedSecondBase) := by
    rw [hmask, hfive]
    exact one_bit_exact_selected
  have hzero : hiddenMismatchMass K chosenInput chosenOutput
      selectedSecondBase separatingMask = 0 := by
    have heq := candidate_eq_five_add_hidden K chosenInput chosenOutput
      selectedSecondBase separatingMask
    rw [hexact] at heq
    omega
  refine ⟨?_, hexact, hzero, ?_⟩
  · rw [hfive]
    exact selected_five_positive
  · rw [hgain]
    exact selected_gain_positive

open scoped Classical in
/-- The zero-bit observation really remains inexact on this same
nonempty restricted fiber, uniformly over the five-subkey family. -/
theorem zero_bit_hidden_positive_for_family
    (K : Master) (h : sameFirstFive K) :
    0 < hiddenMismatchMass K chosenInput chosenOutput
      selectedSecondBase emptyMask := by
  classical
  have hx := exact_one_bit_for_family K h
  have hd := coarse_hidden_eq_fine_add_gain K chosenInput chosenOutput
    selectedSecondBase emptyMask separatingMask masks_ordered
  rw [hx.2.2.1] at hd
  omega

open scoped Classical in
/-- The whole difference between zero-bit and one-bit candidates is
a real positive false-join mass, not an artificial positive weight. -/
theorem one_bit_strictly_better_for_family
    (K : Master) (h : sameFirstFive K) :
    maskCandidateMass K chosenInput chosenOutput selectedSecondBase
      separatingMask <
    maskCandidateMass K chosenInput chosenOutput selectedSecondBase
      emptyMask := by
  classical
  have hx := exact_one_bit_for_family K h
  have hd := coarse_candidate_eq_fine_add_gain K chosenInput chosenOutput
    selectedSecondBase emptyMask separatingMask masks_ordered
  omega

end Magma.DiffanFiveRoundTwoBaseExactMask
