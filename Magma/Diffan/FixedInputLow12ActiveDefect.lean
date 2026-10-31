module

import all Init.Data.Range.Basic
public import Magma.Diffan.FixedInputLow12Factor
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Active false joins for the 12-bit fixed-input observation

The low-12 congruence certificate is an exact statement about the
OBSERVED reconstructed difference, but it does not make the low-12
label a sufficient join state. We construct two *genuine* four-round
windows sharing the observed low-12 label but not the complete first
common StateDifference, even while retaining the other base word and
both full difference words.

Unlike a witness with completely unrestricted endpoints, the left
input difference is fixed to any prescribed value `a`, and the right
output difference is fixed to the value produced by its actual window.
-/

namespace Magma.DiffanFixedInputLow12ActiveDefect

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFixedInputLow12Factor
open Magma.DiffanTwoRoundRawOutputMasks

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- The short label that suffices to compute the observed (masked)
first-common difference at a fixed input difference. -/
def low12JoinLabel (m : Point) : Word := low12Base m.base

/-- Change the first base word OUTSIDE the observed 12 bits.
Keep the second base word and the entire difference unchanged. -/
def highFirstMate (m : Point) : Point :=
  ⟨(m.base.1 ^^^ (0x00001000#32), m.base.2), m.delta⟩

@[simp]
theorem highFirstMate_label (m : Point) : low12JoinLabel (highFirstMate m) = low12JoinLabel m := by
  change ((m.base.1 ^^^ (0x00001000#32)) &&& inputLow12Mask) = (m.base.1 &&& inputLow12Mask)
  unfold inputLow12Mask
  bv_decide

/-- Even retaining the second base word AND the complete difference
would not distinguish this pair. -/
theorem highFirstMate_other_fields (m : Point) :
    (highFirstMate m).base.2 = m.base.2 ∧
      (highFirstMate m).delta = m.delta := ⟨rfl, rfl⟩

/-- The two full first-common points are genuinely distinct. -/
theorem highFirstMate_ne (m : Point) : m ≠ highFirstMate m := by
  have hword : m.base.1 ≠ m.base.1 ^^^ (0x00001000#32) := by
    bv_decide
  intro h
  exact hword (congrArg (fun p : Point => p.base.1) h)

open scoped Classical in
/-- A left window whose input differential is fixed to `a` is
realized by running the same scheduled round functions from `p`. -/
theorem fixed_input_left_pos (master : Master) (a : RoundState)
    (p : Point) (hpa : p.delta = a) :
    0 < leftWeight master (inputDifference a) unrestricted
      (leftFrom master p).p₁ := by
  classical
  change 0 < Fintype.card
    (LeftAt master (inputDifference a) unrestricted
      (leftFrom master p).p₁)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom master p, ⟨hpa, trivial⟩⟩, rfl⟩⟩

open scoped Classical in
/-- For any first-common point, the genuine right window determines
an output difference for which the right conditional mass is positive. -/
theorem fixed_output_right_pos (master : Master) (n : Point) :
    0 < rightWeight master
      (outputDifference (rightFrom master n).p₄.delta) n := by
  classical
  change 0 < Fintype.card
    (RightAt master
      (outputDifference (rightFrom master n).p₄.delta) n)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨rightFrom master n, rfl⟩, rfl⟩⟩

open scoped Classical in
/-- Even with a completely specified left input difference and a
completely specified right output difference, the 12-bit label can
identify two different active common points. The output difference
is obtained from the concrete right witness and can depend on master. -/
theorem active_low12_false_join (master : Master) (a : RoundState) :
    ∃ b : RoundState, ∃ m n : Point,
      low12JoinLabel m = low12JoinLabel n ∧
      m ≠ n ∧
      0 < leftWeight master (inputDifference a) unrestricted m ∧
      0 < rightWeight master (outputDifference b) n := by
  let p : Point := ⟨((0#32), (0#32)), a⟩
  let m : Point := (leftFrom master p).p₁
  let n : Point := highFirstMate m
  let b : RoundState := (rightFrom master n).p₄.delta
  refine ⟨b, m, n, ?_, ?_, ?_, ?_⟩
  · exact (highFirstMate_label m).symm
  · exact highFirstMate_ne m
  · exact fixed_input_left_pos master a p rfl
  · exact fixed_output_right_pos master n

open scoped Classical in
/-- Thus the coarse join strictly overcounts genuine paths in some
fixed-output slice, for *every* master key and *every* fixed input
difference, including nonzero differences. -/
theorem low12_fixed_endpoints_defect_positive (master : Master)
    (a : RoundState) :
    ∃ b : RoundState,
      0 < Diffan.LabelJoinDefect.defectMass low12JoinLabel
        (leftWeight master (inputDifference a) unrestricted)
        (rightWeight master (outputDifference b)) := by
  classical
  rcases active_low12_false_join master a with
    ⟨b, m, n, hlabel, hne, hleft, hright⟩
  refine ⟨b, ?_⟩
  by_contra hnot
  have hz : Diffan.LabelJoinDefect.defectMass low12JoinLabel
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master (outputDifference b)) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hzero :=
    (Diffan.LabelJoinDefect.defect_eq_zero_iff low12JoinLabel
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master (outputDifference b))).mp hz m n hlabel hne
  have hpositive : 0 <
      leftWeight master (inputDifference a) unrestricted m *
        rightWeight master (outputDifference b) n :=
    Nat.mul_pos hleft hright
  omega

open scoped Classical in
/-- The defect is a genuine overcount of the true five-round count,
not merely a failure of injectivity in a projected state space. -/
theorem low12_fixed_endpoints_coarse_strict (master : Master)
    (a : RoundState) :
    ∃ b : RoundState,
      Fintype.card
        (FiveRestricted master (inputDifference a)
          (outputDifference b) unrestricted) <
      Diffan.LabelJoinDefect.coarseMass low12JoinLabel
        (leftWeight master (inputDifference a) unrestricted)
        (rightWeight master (outputDifference b)) := by
  classical
  rcases low12_fixed_endpoints_defect_positive master a with ⟨b, hp⟩
  refine ⟨b, ?_⟩
  have hsum := five_coarse_eq_real_plus_defect master
    (inputDifference a) (outputDifference b) unrestricted low12JoinLabel
  omega

open scoped Classical in
/-- Concrete, prescribed nonzero input differential. The output
slice is still chosen after constructing the genuine right window. -/
theorem nonzero_fixed_input_coarse_strict (master : Master) :
    ∃ b : RoundState,
      Fintype.card
        (FiveRestricted master
          (inputDifference ((1#32), (1#32)))
          (outputDifference b) unrestricted) <
      Diffan.LabelJoinDefect.coarseMass low12JoinLabel
        (leftWeight master
          (inputDifference ((1#32), (1#32))) unrestricted)
        (rightWeight master (outputDifference b)) := by
  exact low12_fixed_endpoints_coarse_strict master ((1#32), (1#32))

end Magma.DiffanFixedInputLow12ActiveDefect
