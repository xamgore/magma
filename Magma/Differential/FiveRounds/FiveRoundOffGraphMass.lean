module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundFixedInputGraphDefect
public import Difan.Fibers.GraphDefectMass

@[expose] public section

/-!
# Five real Magma rounds: exact basewise off-graph correction

For a fixed (including nonzero) input difference `a`, the first
shared point of the left four-round window lies on
`reconstructed master a`. The corresponding coarse base-label join
may still overcount right windows, but the overcount has an exact
conditional formula indexed only by the 64-bit common base.

This uses the same scheduled 256-bit master key for both windows.
The result never treats per-round DDTs as independent.
-/

namespace Magma.DifanFiveRoundOffGraphMass

open Magma
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundLabelJoinDefect
open Magma.DifanFiveRoundBaseDeltaLabelAudit
open Magma.DifanFiveRoundFixedInputGraphJoin
open Magma.DifanFiveRoundZeroBoundaryBaseLabel

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- The exact right-window mass with the same base `b` but a different
full common StateDifference than the one predicted by the left window. -/
noncomputable def rightOffGraph (master : Master)
    (a : RoundState) (Q : Point → Prop) (b : RoundState) : Nat := by
  classical
  exact Difan.GraphDefectMass.offGraphRightMass
    (fun m : Point => m.base)
    (reconstructed master a)
    (rightWeight master Q) b

open scoped Classical in
/-- The *entire* base-label overcount is the weighted sum of right
off-graph masses. No auxiliary midpoint mask or key scan is needed. -/
theorem five_base_defect_exact
    (master : Master) (a : RoundState) (Q R : Point → Prop) :
    Difan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master Q) =
    ∑ b : RoundState,
      leftWeight master (inputDifference a) R
        (reconstructed master a b) * rightOffGraph master a Q b := by
  classical
  exact Difan.GraphDefectMass.defect_eq_sum_offGraph
    (fun m : Point => m.base)
    (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R)

open scoped Classical in
/-- A complete quantitative correction of the coarse five-round join:
all terms still belong to real windows of ONE master key. -/
theorem five_base_coarse_eq_real_add_offGraph
    (master : Master) (a : RoundState) (Q R : Point → Prop) :
    Difan.LabelJoinDefect.coarseMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master Q) =
    Fintype.card (FiveRestricted master (inputDifference a) Q R) +
      ∑ b : RoundState,
        leftWeight master (inputDifference a) R
          (reconstructed master a b) * rightOffGraph master a Q b := by
  classical
  calc
    _ = Fintype.card (FiveRestricted master (inputDifference a) Q R) +
        Difan.LabelJoinDefect.defectMass baseLabel
          (leftWeight master (inputDifference a) R)
          (rightWeight master Q) :=
      five_coarse_eq_real_plus_defect master
        (inputDifference a) Q R baseLabel
    _ = _ := by rw [five_base_defect_exact master a Q R]

open scoped Classical in
/-- Losslessness of the base label is a per-base, weighted absence of
right continuations outside the reconstructed graph. -/
theorem five_base_exact_iff_every_offGraph_term_zero
    (master : Master) (a : RoundState) (Q R : Point → Prop) :
    Difan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master Q) = 0 ↔
    ∀ b : RoundState,
      leftWeight master (inputDifference a) R
        (reconstructed master a b) * rightOffGraph master a Q b = 0 := by
  classical
  exact Difan.GraphDefectMass.defect_zero_iff_local
    (fun m : Point => m.base)
    (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R)

open scoped Classical in
/-- One active base with positive off-graph right weight gives a
strictly positive quantitative overcount for this five-round slice. -/
theorem five_base_defect_pos_of_one_base
    (master : Master) (a : RoundState) (Q R : Point → Prop)
    (b : RoundState)
    (hleft : 0 < leftWeight master (inputDifference a) R
      (reconstructed master a b))
    (hright : 0 < rightOffGraph master a Q b) :
    0 < Difan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) R)
      (rightWeight master Q) := by
  exact Difan.GraphDefectMass.defect_pos_of_local_mass
    (fun m : Point => m.base)
    (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R) b hleft hright

end Magma.DifanFiveRoundOffGraphMass
