module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundMiddleFiberMass
public import Difan.Fibers.LabelJoinDefect

@[expose] public section

/-!
# An exact error certificate for coarse five-round window joins

This applies the generic label-join defect to the actual conditional masses
of two overlapping four-round Magma windows. Their five-round trajectories
use the same master key. No independent-round-key or marginal-DDT product
assumption is introduced.
-/

namespace Magma.DifanFiveRoundLabelJoinDefect

open Magma
open Magma.DifanFiveRoundMiddleFiberMass
open Magma.DifanFiveRoundOverlappingWindows

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Actual multiplicities of two real four-round windows at a full point. -/
noncomputable def leftWeight (master : Master) (P R : Point → Prop) (m : Point) : Nat :=
  by classical exact Fintype.card (LeftAt master P R m)

noncomputable def rightWeight (master : Master) (Q : Point → Prop) (m : Point) : Nat := by
  classical exact Fintype.card (RightAt master Q m)

open scoped Classical in
/-- Counting matches by a coarse label, rather than by the complete
common point, gives the genuine five-round path count plus a NONNEGATIVE
number of false cross-window matches. -/
theorem five_coarse_eq_real_plus_defect
    (master : Master) (P Q R : Point → Prop)
    {Label : Type*} [DecidableEq Label] (observe : Point → Label) :
    Difan.LabelJoinDefect.coarseMass observe
        (leftWeight master P R) (rightWeight master Q) =
      Fintype.card (FiveRestricted master P Q R) +
        Difan.LabelJoinDefect.defectMass observe
          (leftWeight master P R) (rightWeight master Q) := by
  classical
  have htotal :
      Difan.LabelJoinDefect.exactMass
          (leftWeight master P R) (rightWeight master Q) =
        Fintype.card (FiveRestricted master P Q R) := by
    calc
      _ = ∑ m : Point, conditionalMass master P Q R m := by
        rfl
      _ = _ := (five_count_eq_conditional_mass master P Q R).symm
  calc
    _ = Difan.LabelJoinDefect.exactMass
          (leftWeight master P R) (rightWeight master Q) +
        Difan.LabelJoinDefect.defectMass observe
          (leftWeight master P R) (rightWeight master Q) :=
      Difan.LabelJoinDefect.coarse_eq_exact_add_defect observe
        (leftWeight master P R) (rightWeight master Q)
    _ = _ := by rw [htotal]

open scoped Classical in
/-- Exactness requires that two active windows with the same label have
no distinct complete middle points. This criterion depends on the actual
reachable fibers, not on the width of `Label` alone. -/
theorem five_coarse_exact_iff
    (master : Master) (P Q R : Point → Prop)
    {Label : Type*} [DecidableEq Label] (observe : Point → Label) :
    Difan.LabelJoinDefect.coarseMass observe
        (leftWeight master P R) (rightWeight master Q) =
      Fintype.card (FiveRestricted master P Q R) ↔
    ∀ m n : Point, observe m = observe n → m ≠ n →
      leftWeight master P R m * rightWeight master Q n = 0 := by
  classical
  have hs := five_coarse_eq_real_plus_defect master P Q R observe
  constructor
  · intro heq
    have hz : Difan.LabelJoinDefect.defectMass observe
        (leftWeight master P R) (rightWeight master Q) = 0 := by
      omega
    exact (Difan.LabelJoinDefect.defect_eq_zero_iff observe
      (leftWeight master P R) (rightWeight master Q)).mp hz
  · intro h
    have hz := (Difan.LabelJoinDefect.defect_eq_zero_iff observe
      (leftWeight master P R) (rightWeight master Q)).mpr h
    rw [hs, hz]
    simp

end Magma.DifanFiveRoundLabelJoinDefect
