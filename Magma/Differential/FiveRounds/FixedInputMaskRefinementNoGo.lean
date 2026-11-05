module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FixedInputLow12ActiveDefect
public import Diffan.Fibers.LabelRefinementDefect
import Std.Tactic.BVDecide

@[expose] public section

/-!
# A universal obstruction to dropping first-base bits at a five-round join

We retain the second full base word AND BOTH full difference words.
Even then, omitting any bit of the first base word admits active false
joins in some fixed-output slice, for every master key and fixed input
difference. A richer mask strictly eliminates some such joins, but in
general does not eliminate all of them.

The output difference may depend on the master key; no uniform output
witness across all keys is asserted.
-/

namespace Magma.DiffanFixedInputMaskRefinementNoGo

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFixedInputLow12ActiveDefect

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Keep the entire second base and complete difference, but project the
first base through `mask`. -/
def richMaskLabel (mask : Word) (m : Point) : (Word × Word) × RoundState :=
  ((m.base.1 &&& mask, m.base.2), m.delta)

/-- Change only the first base coordinate. -/
def maskMate (t : Word) (m : Point) : Point :=
  ⟨(m.base.1 ^^^ t, m.base.2), m.delta⟩

/-- A shift supported outside `mask` is invisible to the rich label. -/
theorem maskMate_label (mask t : Word) (ht : t &&& mask = 0#32)
    (m : Point) : richMaskLabel mask (maskMate t m) = richMaskLabel mask m := by
  have h : ((m.base.1 ^^^ t) &&& mask) = (m.base.1 &&& mask) := by
    bv_decide
  change (((m.base.1 ^^^ t) &&& mask, m.base.2), m.delta) =
    ((m.base.1 &&& mask, m.base.2), m.delta)
  rw [h]

/-- A nonzero shift always changes the full common point. -/
theorem maskMate_ne (t : Word) (ht : t ≠ 0#32) (m : Point) :
    m ≠ maskMate t m := by
  have hw : m.base.1 ≠ m.base.1 ^^^ t := by
    bv_decide
  intro h
  exact hw (congrArg (fun q : Point => q.base.1) h)

open scoped Classical in
/-- The only obstruction needed is ONE omitted nonzero shift. The left
and right windows are genuine trajectories using the same schedule. -/
theorem rich_mask_active_false_join (master : Master) (a : RoundState)
    (mask t : Word) (ht : t ≠ 0#32) (hmask : t &&& mask = 0#32) :
    ∃ b : RoundState, ∃ m n : Point,
      richMaskLabel mask m = richMaskLabel mask n ∧ m ≠ n ∧
      0 < leftWeight master (inputDifference a) unrestricted m ∧
      0 < rightWeight master (outputDifference b) n := by
  let p : Point := ⟨((0#32), (0#32)), a⟩
  let m : Point := (leftFrom master p).p₁
  let n : Point := maskMate t m
  let b : RoundState := (rightFrom master n).p₄.delta
  refine ⟨b, m, n, ?_, ?_, ?_, ?_⟩
  · exact (maskMate_label mask t hmask m).symm
  · exact maskMate_ne t ht m
  · exact fixed_input_left_pos master a p rfl
  · exact fixed_output_right_pos master n

open scoped Classical in
/-- No mask that omits the supported nonzero direction `t` is a
universally sufficient join label, EVEN when the other coordinates
are preserved in full. -/
theorem rich_mask_defect_positive (master : Master) (a : RoundState)
    (mask t : Word) (ht : t ≠ 0#32) (hmask : t &&& mask = 0#32) :
    ∃ b : RoundState,
      0 < Diffan.LabelJoinDefect.defectMass (richMaskLabel mask)
        (leftWeight master (inputDifference a) unrestricted)
        (rightWeight master (outputDifference b)) := by
  classical
  rcases rich_mask_active_false_join master a mask t ht hmask with
    ⟨b, m, n, hc, hne, hL, hR⟩
  refine ⟨b, ?_⟩
  by_contra hnot
  have hz : Diffan.LabelJoinDefect.defectMass (richMaskLabel mask)
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master (outputDifference b)) = 0 := Nat.eq_zero_of_not_pos hnot
  have hterm :=
    (Diffan.LabelJoinDefect.defect_eq_zero_iff (richMaskLabel mask)
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master (outputDifference b))).mp hz m n hc hne
  have hp : 0 < leftWeight master (inputDifference a) unrestricted m *
      rightWeight master (outputDifference b) n := Nat.mul_pos hL hR
  omega

/-- A proper mask always has a nonzero direction supported outside it. -/
theorem complement_nonzero_of_proper (mask : Word)
    (h : mask ≠ (0xFFFFFFFF#32)) :
    (~~~mask) ≠ 0#32 := by
  bv_decide

open scoped Classical in
/-- Global no-go theorem for all proper 32-bit first-base masks.
The fixed input difference is arbitrary, including nonzero ones. -/
theorem every_proper_first_mask_has_defect (master : Master)
    (a : RoundState) (mask : Word) (h : mask ≠ (0xFFFFFFFF#32)) :
    ∃ b : RoundState,
      0 < Diffan.LabelJoinDefect.defectMass (richMaskLabel mask)
        (leftWeight master (inputDifference a) unrestricted)
        (rightWeight master (outputDifference b)) := by
  have ht : (~~~mask) ≠ 0#32 := complement_nonzero_of_proper mask h
  have horth : (~~~mask) &&& mask = 0#32 := by bv_decide
  exact rich_mask_defect_positive master a mask (~~~mask) ht horth

/-- Including bit 12 distinguishes points related by a bit-12 shift. -/
theorem bit12_visible_at_low13 (m : Point) :
    richMaskLabel (0x00001FFF#32) m ≠
      richMaskLabel (0x00001FFF#32) (maskMate (0x00001000#32) m) := by
  intro heq
  have hfirst := congrArg (fun z : (Word × Word) × RoundState => z.1.1) heq
  change (m.base.1 &&& (0x00001FFF#32)) =
    ((m.base.1 ^^^ (0x00001000#32)) &&& (0x00001FFF#32)) at hfirst
  bv_decide

/-- The 13-bit mask refines the 12-bit mask, without changing
any other component of the label. -/
theorem low13_refines_low12 (m n : Point)
    (h : richMaskLabel (0x00001FFF#32) m =
      richMaskLabel (0x00001FFF#32) n) :
    richMaskLabel (0x00000FFF#32) m =
      richMaskLabel (0x00000FFF#32) n := by
  have hfirst := congrArg (fun z : (Word × Word) × RoundState => z.1.1) h
  have hsecond := congrArg (fun z : (Word × Word) × RoundState => z.1.2) h
  have hdelta := congrArg (fun z : (Word × Word) × RoundState => z.2) h
  have hlow : (m.base.1 &&& (0x00000FFF#32)) =
      (n.base.1 &&& (0x00000FFF#32)) := by
    change (m.base.1 &&& (0x00001FFF#32)) =
      (n.base.1 &&& (0x00001FFF#32)) at hfirst
    bv_decide
  change ((m.base.1 &&& (0x00000FFF#32), m.base.2), m.delta) =
    ((n.base.1 &&& (0x00000FFF#32), n.base.2), n.delta)
  change m.base.2 = n.base.2 at hsecond
  change m.delta = n.delta at hdelta
  rw [hlow, hsecond, hdelta]

open scoped Classical in
/-- Adding bit 12 strictly removes positive false-join mass in a
suitable fixed-output slice, for EVERY master and fixed input difference. -/
theorem low13_strictly_improves_low12 (master : Master) (a : RoundState) :
    ∃ b : RoundState,
      Diffan.LabelJoinDefect.defectMass (richMaskLabel (0x00001FFF#32))
          (leftWeight master (inputDifference a) unrestricted)
          (rightWeight master (outputDifference b)) <
      Diffan.LabelJoinDefect.defectMass (richMaskLabel (0x00000FFF#32))
          (leftWeight master (inputDifference a) unrestricted)
          (rightWeight master (outputDifference b)) := by
  classical
  let p : Point := ⟨((0#32), (0#32)), a⟩
  let m : Point := (leftFrom master p).p₁
  let n : Point := maskMate (0x00001000#32) m
  let b : RoundState := (rightFrom master n).p₄.delta
  have hc : richMaskLabel (0x00000FFF#32) m =
      richMaskLabel (0x00000FFF#32) n := by
    exact (maskMate_label (0x00000FFF#32) (0x00001000#32) (by decide) m).symm
  have hf : richMaskLabel (0x00001FFF#32) m ≠
      richMaskLabel (0x00001FFF#32) n := bit12_visible_at_low13 m
  have hL : 0 < leftWeight master (inputDifference a) unrestricted m :=
    fixed_input_left_pos master a p rfl
  have hR : 0 < rightWeight master (outputDifference b) n :=
    fixed_output_right_pos master n
  refine ⟨b, ?_⟩
  exact Diffan.LabelRefinementDefect.defect_refinement_strict_of_witness
    (richMaskLabel (0x00000FFF#32)) (richMaskLabel (0x00001FFF#32))
    low13_refines_low12
    (leftWeight master (inputDifference a) unrestricted)
    (rightWeight master (outputDifference b)) m n hc hf hL hR

open scoped Classical in
/-- Although adding bit 12 helps, the 13-bit rich label is still NOT
universally sufficient: bit 13 remains omitted. -/
theorem low13_still_has_active_false_joins (master : Master) (a : RoundState) :
    ∃ b : RoundState,
      0 < Diffan.LabelJoinDefect.defectMass (richMaskLabel (0x00001FFF#32))
        (leftWeight master (inputDifference a) unrestricted)
        (rightWeight master (outputDifference b)) := by
  exact rich_mask_defect_positive master a (0x00001FFF#32)
    (0x00002000#32) (by decide) (by decide)

end Magma.DiffanFixedInputMaskRefinementNoGo
