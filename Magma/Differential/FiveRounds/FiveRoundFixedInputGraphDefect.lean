module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FixedInputMaskRefinementNoGo
public import Difan.Fibers.GraphLabelExactness

@[expose] public section

/-!
# A right off-graph certificate for exact five-round base labels

For a fixed input difference `a`, the left four-round window has its
first common StateDifference on the graph of `reconstructed master a`.
Consequently, checking a base-only join needs only one kind of test:
can the right four-round window have a *different difference* at the
same base when the left graph point is active?

This reduces a general pairwise label-defect problem to a single graph
and a right conditional support.  It works for nonzero input differences
and arbitrary output and middle predicates, all under one master key.
-/

namespace Magma.DifanFiveRoundFixedInputGraphDefect

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundLabelJoinDefect
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundZeroBoundaryBaseLabel
open Magma.DifanFiveRoundFixedInputGraphJoin

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

open scoped Classical in
/-- The base-only label is exact iff every active right point outside
the predicted graph has zero joint weight with the left graph point. -/
theorem base_exact_iff_off_graph_zero
    (master : Master) (a : RoundState) (Q R : Point → Prop) :
    Difan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) =
      Fintype.card (FiveRestricted master (inputDifference a) Q R) ↔
    ∀ b (n : Point), n.base = b →
      n ≠ reconstructed master a b →
      leftWeight master (inputDifference a) R
        (reconstructed master a b) * rightWeight master Q n = 0 := by
  classical
  have hcore := Difan.GraphLabelExactness.graph_coarse_eq_exact_iff
    (fun m : Point => m.base) (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R)
  have hreal := five_coarse_eq_real_plus_defect master
    (inputDifference a) Q R baseLabel
  constructor
  · intro heq
    have hzero : Difan.LabelJoinDefect.defectMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) = 0 := by omega
    have heqexact : Difan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) =
        Difan.LabelJoinDefect.exactMass
          (leftWeight master (inputDifference a) R)
          (rightWeight master Q) := by
      rw [Difan.LabelJoinDefect.coarse_eq_exact_add_defect, hzero]
      simp
    exact hcore.mp heqexact
  · intro h
    have heqexact : Difan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) =
        Difan.LabelJoinDefect.exactMass
          (leftWeight master (inputDifference a) R)
          (rightWeight master Q) := hcore.mpr h
    have hzero : Difan.LabelJoinDefect.defectMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) = 0 := by
      have hsplit := Difan.LabelJoinDefect.coarse_eq_exact_add_defect
        baseLabel (leftWeight master (inputDifference a) R)
        (rightWeight master Q)
      omega
    rw [hreal, hzero]
    simp

open scoped Classical in
/-- A concrete active right point away from the reconstructed left
graph proves a strictly positive base-label defect, without counting
all middle points. -/
theorem base_defect_pos_of_off_graph_witness
    (master : Master) (a : RoundState) (Q R : Point → Prop)
    (b : RoundState) (n : Point)
    (hb : n.base = b)
    (hne : n ≠ reconstructed master a b)
    (hL : 0 < leftWeight master (inputDifference a) R
      (reconstructed master a b))
    (hR : 0 < rightWeight master Q n) :
    0 < Difan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master Q) := by
  exact Difan.GraphLabelExactness.graph_defect_pos_of_witness
    (fun m : Point => m.base) (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R)
    b n hb hne hL hR

open scoped Classical in
/-- The same test specialized to fixed (possibly nonzero) DIFFERENCES
at both outer endpoints, while keeping the middle condition arbitrary. -/
theorem fixed_boundary_base_exact_iff
    (master : Master) (a outDelta : RoundState) (R : Point → Prop) :
    Difan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master (inputDifference a) R)
        (rightWeight master (outputDifference outDelta)) =
      Fintype.card
        (FiveRestricted master (inputDifference a)
          (outputDifference outDelta) R) ↔
    ∀ b (n : Point), n.base = b →
      n ≠ reconstructed master a b →
      leftWeight master (inputDifference a) R
        (reconstructed master a b) *
        rightWeight master (outputDifference outDelta) n = 0 := by
  exact base_exact_iff_off_graph_zero master a (outputDifference outDelta) R

end Magma.DifanFiveRoundFixedInputGraphDefect
