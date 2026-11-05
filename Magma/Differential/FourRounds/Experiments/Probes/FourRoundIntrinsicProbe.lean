module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundProjectionDefect

@[expose] public section

/-!
# Intrinsic rectangularity of the zero-boundary four-round Magma fiber

The previously found positive projection defect comes from imposing a
nonrectangular condition on the midpoint.  For the unmasked, unrestricted
four-round slice (aL, 0) -> (0, bR), the genuine middle fiber is instead
rectangular for every 256-bit master key and arbitrary aL, bR.

This file makes the *pointwise* reason explicit.  The right input
difference is determined by g[k1] at the middle-left base word; the left
output difference is determined by g[k2] at the middle-right base word.
When both are zero, the two conditions separate.  No marginal-DDT
independence is postulated.
-/

namespace Magma.DifanFourRoundIntrinsicRectangularity

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFourRoundScheduledMiddleFibers
open Magma.DifanFourRoundForcedMiddleDifference
open Magma.DifanFourRoundMiddleCoordinateKernel
open Magma.DifanFourRoundProjectionDefect

private abbrev Word := V 32
private abbrev Master := V 256
private abbrev RoundState := Word × Word
private abbrev Point := Difan.StateDifference RoundState RoundState

private theorem xor_eq_zero_iff (x y : Word) :
    (x ^^^ y) = (0#32) ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z : Word => z ^^^ y) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.zero_xor] using hh
  · rintro rfl
    exact BitVec.xor_self

private theorem step_base_left (k : Word) (p : Point) :
    (step k p).base.1 = p.base.2 := rfl

/-- The right input difference, reconstructed from the complete midpoint.
The outer first-round key does not occur in the formula. -/
theorem prefix_input_right (master : Master) (mid : Point) :
    ((left master).symm mid).delta.2 =
      (gDifference (roundKey master (1 : Fin 32))
         mid.base.1 mid.delta.1) ^^^ mid.delta.2 := by
  let p : Point := (left master).symm mid
  let z : Point := step (roundKey master (0 : Fin 32)) p
  have heq : step (roundKey master (1 : Fin 32)) z = mid := by
    change step (roundKey master (1 : Fin 32))
      (step (roundKey master (0 : Fin 32)) ((left master).symm mid)) = mid
    rw [← left_eq_two_steps]
    exact (left master).apply_symm_apply mid
  have hu : z.base.2 = mid.base.1 := by
    have h := congrArg (fun q : Point => q.base.1) heq
    simpa only [step_base_left] using h
  have ha : z.delta.2 = mid.delta.1 := by
    have h := congrArg (fun q : Point => q.delta.1) heq
    rw [step_left] at h
    exact h
  have hd : z.delta.1 = p.delta.2 := step_left _ p
  have hright := congrArg (fun q : Point => q.delta.2) heq
  rw [step_delta] at hright
  change
    ((g (roundKey master (1 : Fin 32)) (z.base.2 ^^^ z.delta.2) ^^^
      g (roundKey master (1 : Fin 32)) z.base.2) ^^^ z.delta.1) =
      mid.delta.2 at hright
  rw [hu, ha, hd] at hright
  let e : Word := gDifference (roundKey master (1 : Fin 32))
    mid.base.1 mid.delta.1
  have h : e ^^^ p.delta.2 = mid.delta.2 := by
    change e ^^^ p.delta.2 = mid.delta.2 at hright
    exact hright
  change p.delta.2 = e ^^^ mid.delta.2
  calc
    p.delta.2 = e ^^^ (e ^^^ p.delta.2) := by
      simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    _ = e ^^^ mid.delta.2 := congrArg (fun w : Word => e ^^^ w) h

/-- The left output difference is determined by the middle-right base
and the third-round key, independently of the outer final-round key. -/
theorem suffix_output_left (master : Master) (mid : Point) :
    (right master mid).delta.1 =
      (gDifference (roundKey master (2 : Fin 32))
         mid.base.2 mid.delta.2) ^^^ mid.delta.1 := by
  rw [right_eq_two_steps, step_left, step_delta]
  rfl

/-- Suppressing the right input difference forces the input-left
half to equal the fixed middle-left difference. -/
private theorem prefix_delta_of_zero_right
    (master : Master) (aL bR u v : Word)
    (h : ((left master).symm
      (⟨(u, v), (aL, bR)⟩ : Point)).delta.2 = (0#32)) :
    ((left master).symm
      (⟨(u, v), (aL, bR)⟩ : Point)).delta = (aL, 0#32) := by
  let mid : Point := ⟨(u, v), (aL, bR)⟩
  let p : Point := (left master).symm mid
  have hleft := two_steps_left_of_zero_input_right
    (roundKey master (0 : Fin 32))
    (roundKey master (1 : Fin 32)) p h
  rw [← left_eq_two_steps] at hleft
  have heq : left master p = mid := (left master).apply_symm_apply mid
  rw [heq] at hleft
  exact Prod.ext hleft.symm h

/-- Suppressing the left output difference forces the output-right
half to equal the fixed middle-right difference. -/
private theorem suffix_delta_of_zero_left
    (master : Master) (aL bR u v : Word)
    (h : (right master (⟨(u, v), (aL, bR)⟩ : Point)).delta.1 = (0#32)) :
    (right master (⟨(u, v), (aL, bR)⟩ : Point)).delta = (0#32, bR) := by
  let mid : Point := ⟨(u, v), (aL, bR)⟩
  have hright : (right master mid).delta.2 = mid.delta.2 := by
    rw [right_eq_two_steps]
    apply two_steps_right_of_zero_output_left
    simpa only [right_eq_two_steps] using h
  exact Prod.ext h hright

/-- Pointwise splitting certificate for the unrestricted four-round
midpoint. This is stronger than merely knowing an equality of totals. -/
theorem unmasked_admissible_iff (master : Master)
    (aL bR u v : Word) :
    admissible master aL bR (0#32) (0#32) (fun _ => True) u v ↔
      gDifference (roundKey master (1 : Fin 32)) u aL = bR ∧
      gDifference (roundKey master (2 : Fin 32)) v bR = aL := by
  let mid : Point := ⟨(u, v), (aL, bR)⟩
  have hp :
      ((left master).symm mid).delta = (aL, 0#32) ↔
      ((left master).symm mid).delta.2 = (0#32) := by
    constructor
    · intro hh
      exact congrArg Prod.snd hh
    · intro hh
      exact prefix_delta_of_zero_right master aL bR u v hh
  have hq :
      (right master mid).delta = (0#32, bR) ↔
      (right master mid).delta.1 = (0#32) := by
    constructor
    · intro hh
      exact congrArg Prod.fst hh
    · intro hh
      exact suffix_delta_of_zero_left master aL bR u v hh
  change
    (((left master).symm mid).delta = (aL, 0#32) ∧
      (((left master).symm mid).base.2 &&& (0#32)) = (0#32)) ∧
    True ∧
    ((right master mid).delta = (0#32, bR) ∧
      ((right master mid).base.1 &&& (0#32)) = (0#32)) ↔ _
  constructor
  · intro hh
    have hl : ((left master).symm mid).delta = (aL, 0#32) := hh.1.1
    have hr : (right master mid).delta = (0#32, bR) := hh.2.2.1
    have hleft := hp.mp hl
    have hright := hq.mp hr
    rw [prefix_input_right] at hleft
    rw [suffix_output_left] at hright
    exact ⟨(xor_eq_zero_iff _ _).mp hleft,
      (xor_eq_zero_iff _ _).mp hright⟩
  · intro hh
    have hleft : ((left master).symm mid).delta.2 = (0#32) := by
      rw [prefix_input_right]
      exact (xor_eq_zero_iff _ _).mpr hh.1
    have hright : (right master mid).delta.1 = (0#32) := by
      rw [suffix_output_left]
      exact (xor_eq_zero_iff _ _).mpr hh.2
    exact ⟨⟨hp.mpr hleft, by simp⟩, trivial,
      ⟨hq.mpr hright, by simp⟩⟩

/-- For every master and *arbitrary* aL,bR, the genuine unmasked
four-round middle fiber is a rectangular product. There is no
intrinsic coordinate-projection defect in this special boundary slice. -/
theorem unmasked_projection_defect_zero (master : Master) (aL bR : Word) :
    missingPairs master aL bR (0#32) (0#32) (fun _ => True) = ∅ := by
  apply missing_empty_of_separation master aL bR (0#32) (0#32)
    (fun _ => True)
    (fun u => gDifference (roundKey master (1 : Fin 32)) u aL = bR)
    (fun v => gDifference (roundKey master (2 : Fin 32)) v bR = aL)
  intro u v
  exact unmasked_admissible_iff master aL bR u v

set_option maxHeartbeats 5000 in
set_option maxRecDepth 100 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option trace.Meta.synthInstance true in
open scoped Classical in
/-- The two real middle coordinates separate exactly, not merely
as independently possible necessary conditions. -/
theorem unmasked_fourRound_product (master : Master) (aL bR : Word) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) (0#32))
      (outputMasked (0#32, bR) (0#32)) (fun _ => True)) =
    Fintype.card {u : Word //
      gDifference (roundKey master (1 : Fin 32)) u aL = bR} *
    Fintype.card {v : Word //
      gDifference (roundKey master (2 : Fin 32)) v bR = aL} := by
  exact fourRound_product_of_separation master aL bR (0#32) (0#32)
    (fun _ => True)
    (fun u => gDifference (roundKey master (1 : Fin 32)) u aL = bR)
    (fun v => gDifference (roundKey master (2 : Fin 32)) v bR = aL)
    (unmasked_admissible_iff master aL bR)

end Magma.DifanFourRoundIntrinsicRectangularity
