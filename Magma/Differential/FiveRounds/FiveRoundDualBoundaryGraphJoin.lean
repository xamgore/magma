module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundOffGraphMass
public import Diffan.Fibers.TwoGraphJoinMass

@[expose] public section

/-!
# Two boundary differences: left and right graphs over the common base

The left four-round window with fixed input difference already has a
unique common difference over each base. Here the right four-round window,
with fixed *output* difference, gets its own graph: each Feistel round
can be reversed on the XOR difference when its input base is known.

The true five-round count is the mass of bases where these two predicted
full points agree. The coarse base-only join adds precisely the bases
where they disagree. All five keys come from one Magma master key.
-/

namespace Magma.DiffanFiveRoundDualBoundaryGraphJoin

open Magma
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFiveRoundOffGraphMass

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Recover the input XOR difference of a single ordinary G round from
its input *base* and its output difference. -/
def inverseRoundDelta (k : Word) (base outputDelta : RoundState) : RoundState :=
  (outputDelta.2 ^^^
    (g k (base.2 ^^^ outputDelta.1) ^^^ g k base.2), outputDelta.1)

/-- No inversion of the nonlinear S-box is needed: the Feistel layout
makes the difference update reversible at a fixed base. -/
theorem inverseRoundDelta_step (k : Word) (p : Point) :
    inverseRoundDelta k p.base (step k p).delta = p.delta := by
  rw [step_delta]
  rcases p with ⟨⟨l, r⟩, ⟨aL, aR⟩⟩
  change
    (((g k (r ^^^ aR) ^^^ g k r) ^^^ aL) ^^^
      (g k (r ^^^ aR) ^^^ g k r), aR) = (aL, aR)
  let t : Word := g k (r ^^^ aR) ^^^ g k r
  change ((t ^^^ aL) ^^^ t, aR) = (aL, aR)
  apply Prod.ext
  · calc
      (t ^^^ aL) ^^^ t = (aL ^^^ t) ^^^ t := by rw [BitVec.xor_comm t aL]
      _ = aL := by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rfl

private theorem next_base_eq (k : Word) (p q p' q' : Point) (hp : step k p = p')
    (hq : step k q = q') (h : p.base = q.base) : p'.base = q'.base := by
  calc
    p'.base = (step k p).base := congrArg (fun x : Point => x.base) hp.symm
    _ = G k p.base := rfl
    _ = G k q.base := by rw [h]
    _ = (step k q).base := rfl
    _ = q'.base := congrArg (fun x : Point => x.base) hq

/-- Run the same *base* trajectory as the right window, but with zero
input difference. Only its four base coordinates are used below. -/
def rightBaseTrack (master : Master) (b : RoundState) :
    FourWindow
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32))
      (roundKey master (4 : Fin 32)) :=
  rightFrom master ⟨b, ((0#32), (0#32))⟩

/-- The backward recursion for the common difference of a right window.
It depends on the *known base track*, one master key, and the required
output difference. It makes no assumption on the initial difference. -/
def rightPredictedDelta (master : Master)
    (outDelta b : RoundState) : RoundState :=
  let z := rightBaseTrack master b
  let d₃ := inverseRoundDelta (roundKey master (4 : Fin 32)) z.p₃.base outDelta
  let d₂ := inverseRoundDelta (roundKey master (3 : Fin 32)) z.p₂.base d₃
  let d₁ := inverseRoundDelta (roundKey master (2 : Fin 32)) z.p₁.base d₂
  inverseRoundDelta (roundKey master (1 : Fin 32)) z.p₀.base d₁

/-- The unique full common point predicted from the output boundary. -/
def rightReconstructed (master : Master)
    (outDelta b : RoundState) : Point :=
  ⟨b, rightPredictedDelta master outDelta b⟩

@[simp]
theorem rightReconstructed_base (master : Master) (outDelta b : RoundState) :
    (rightReconstructed master outDelta b).base = b :=
  rfl

/-- All four bases of two valid windows with the same first base agree.
This is independent of their respective differences. -/
private theorem right_window_bases (master : Master)
    (w : FourWindow
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32))
      (roundKey master (4 : Fin 32)))
    (b : RoundState) (hbase : w.p₀.base = b) :
    w.p₀.base = (rightBaseTrack master b).p₀.base ∧
    w.p₁.base = (rightBaseTrack master b).p₁.base ∧
    w.p₂.base = (rightBaseTrack master b).p₂.base ∧
    w.p₃.base = (rightBaseTrack master b).p₃.base := by
  let z := rightBaseTrack master b
  have h₀ : w.p₀.base = z.p₀.base := hbase
  have h₁ := next_base_eq _ w.p₀ z.p₀ w.p₁ z.p₁ w.h₀ z.h₀ h₀
  have h₂ := next_base_eq _ w.p₁ z.p₁ w.p₂ z.p₂ w.h₁ z.h₁ h₁
  have h₃ := next_base_eq _ w.p₂ z.p₂ w.p₃ z.p₃ w.h₂ z.h₂ h₂
  exact ⟨h₀, h₁, h₂, h₃⟩

/-- A genuine right window with fixed *output* difference is supported
on the backward graph; all intermediate bases are the real ones. -/
theorem right_first_delta_forced (master : Master) (outDelta : RoundState)
    (w : FourWindow
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32))
      (roundKey master (4 : Fin 32)))
    (hout : w.p₄.delta = outDelta) :
    w.p₀.delta = rightPredictedDelta master outDelta w.p₀.base := by
  let z := rightBaseTrack master w.p₀.base
  obtain ⟨hb₀, hb₁, hb₂, hb₃⟩ :=
    right_window_bases master w w.p₀.base rfl
  have hd₃ : w.p₃.delta = inverseRoundDelta
      (roundKey master (4 : Fin 32)) w.p₃.base outDelta := by
    have h := inverseRoundDelta_step (roundKey master (4 : Fin 32)) w.p₃
    rw [w.h₃, hout] at h
    exact h.symm
  have hd₂ : w.p₂.delta = inverseRoundDelta
      (roundKey master (3 : Fin 32)) w.p₂.base w.p₃.delta := by
    have h := inverseRoundDelta_step (roundKey master (3 : Fin 32)) w.p₂
    rw [w.h₂] at h
    exact h.symm
  have hd₁ : w.p₁.delta = inverseRoundDelta
      (roundKey master (2 : Fin 32)) w.p₁.base w.p₂.delta := by
    have h := inverseRoundDelta_step (roundKey master (2 : Fin 32)) w.p₁
    rw [w.h₁] at h
    exact h.symm
  have hd₀ : w.p₀.delta = inverseRoundDelta
      (roundKey master (1 : Fin 32)) w.p₀.base w.p₁.delta := by
    have h := inverseRoundDelta_step (roundKey master (1 : Fin 32)) w.p₀
    rw [w.h₀] at h
    exact h.symm
  calc
    w.p₀.delta = inverseRoundDelta
        (roundKey master (1 : Fin 32)) w.p₀.base w.p₁.delta := hd₀
    _ = rightPredictedDelta master outDelta w.p₀.base := by
      rw [hd₁, hd₂, hd₃, hb₀, hb₁, hb₂, hb₃]
      rfl

open scoped Classical in
/-- The right conditional weight at a fixed output difference has
support on one graph point over each common base. -/
theorem right_active_output_graph (master : Master)
    (outDelta : RoundState) (m : Point)
    (h : 0 < rightWeight master (outputDifference outDelta) m) :
    m = rightReconstructed master outDelta m.base := by
  classical
  change 0 < Fintype.card
    (RightAt master (outputDifference outDelta) m) at h
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp h
  have hb : w.1.1.p₀ = m := w.2
  have hd : w.1.1.p₀.delta =
      rightPredictedDelta master outDelta w.1.1.p₀.base :=
    right_first_delta_forced master outDelta w.1.1 w.1.2
  rw [hb] at hd
  exact (full_point_iff_base_and_difference m
    (rightReconstructed master outDelta m.base)).mpr ⟨rfl, hd⟩

open scoped Classical in
/-- Actual five-round count: at each common base the two reconstructed
full middle points must coincide. There is no marginal DDT product. -/
theorem five_fixed_boundaries_exact_matching_graphs
    (master : Master) (a outDelta : RoundState) (R : Point → Prop) :
    Fintype.card
      (FiveRestricted master (inputDifference a)
        (outputDifference outDelta) R) =
      ∑ b : RoundState,
        if reconstructed master a b = rightReconstructed master outDelta b then
          leftWeight master (inputDifference a) R (reconstructed master a b) *
            rightWeight master (outputDifference outDelta)
              (rightReconstructed master outDelta b)
        else 0 := by
  classical
  calc
    _ = Diffan.LabelJoinDefect.exactMass
        (leftWeight master (inputDifference a) R)
        (rightWeight master (outputDifference outDelta)) := by
      calc
        _ = ∑ m : Point,
          conditionalMass master (inputDifference a)
            (outputDifference outDelta) R m :=
          five_count_eq_conditional_mass master
            (inputDifference a) (outputDifference outDelta) R
        _ = _ := rfl
    _ = _ := Diffan.TwoGraphJoinMass.exact_eq_sum_matching_graphs
      (fun m : Point => m.base)
      (reconstructed master a)
      (rightReconstructed master outDelta)
      (reconstructed_base master a)
      (leftWeight master (inputDifference a) R)
      (rightWeight master (outputDifference outDelta))
      (left_active_graph master a R)
      (right_active_output_graph master outDelta)

open scoped Classical in
/-- The off-graph correction is now a *mismatch syndrome* between two
explicit, deterministically reconstructed differences. -/
theorem five_fixed_boundaries_defect_mismatch
    (master : Master) (a outDelta : RoundState) (R : Point → Prop) :
    Diffan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master (outputDifference outDelta)) =
      ∑ b : RoundState,
        if reconstructed master a b = rightReconstructed master outDelta b then 0
        else
          leftWeight master (inputDifference a) R (reconstructed master a b) *
            rightWeight master (outputDifference outDelta)
              (rightReconstructed master outDelta b) := by
  classical
  exact Diffan.TwoGraphJoinMass.defect_eq_sum_mismatched_graphs
    (fun m : Point => m.base)
    (reconstructed master a)
    (rightReconstructed master outDelta)
    (reconstructed_base master a)
    (rightReconstructed_base master outDelta)
    (leftWeight master (inputDifference a) R)
    (rightWeight master (outputDifference outDelta))
    (left_active_graph master a R)
    (right_active_output_graph master outDelta)

end Magma.DiffanFiveRoundDualBoundaryGraphJoin
