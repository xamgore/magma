module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundZeroBoundaryBaseLabel
public import Diffan.GraphSupportedJoin

@[expose] public section

/-!
# Five scheduled Magma rounds: lossless base indexing for fixed input differences

Fixing the input difference determines the first common difference
from its base, so the exact join admits a base-state index even for
nonzero input differences.

Fix the *input* difference `a` of the LEFT window. If its first common
point has base `(u,v)`, the difference at that point is necessarily

  `(a.2, gDifference (roundKey master 0) u a.2 ^^^ a.1)`.

Thus left mass is supported on the graph of a function of the base.
We may sum the exact join over base states alone, but MUST still test
the right window at the reconstructed full StateDifference.

All round keys come from the same Magma master key.
-/

namespace Magma.DiffanFiveRoundFixedInputGraphJoin

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit
open Magma.DiffanFiveRoundZeroBoundaryBaseLabel

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- The first common difference is a graph over its base as soon as
we fix the left window's input difference. -/
def predictedDelta (master : Master) (a b : RoundState) : RoundState :=
  (a.2, gDifference (roundKey master (0 : Fin 32)) b.1 a.2 ^^^ a.1)

/-- Reconstruct the *whole* first common point from its base. -/
def reconstructed (master : Master) (a b : RoundState) : Point :=
  ⟨b, predictedDelta master a b⟩

/-- A fixed output difference, without restricting its base state. -/
def outputDifference (b : RoundState) (p : Point) : Prop :=
  p.delta = b

@[simp]
theorem reconstructed_base (master : Master) (a b : RoundState) :
    (reconstructed master a b).base = b :=
  rfl

/-- A true four-round left window with fixed input difference has the
predicted difference at its first common point, regardless of the
subsequent three rounds. -/
theorem left_first_difference (master : Master) (a : RoundState)
    (w : FourWindow
      (roundKey master (0 : Fin 32))
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32)))
    (hin : w.p₀.delta = a) :
    w.p₁.delta = predictedDelta master a w.p₁.base := by
  let k : Word := roundKey master (0 : Fin 32)
  have hb : w.p₀.base.2 = w.p₁.base.1 := by
    have hh := congrArg (fun p : Point => p.base.1) w.h₀
    exact hh
  have hd : w.p₁.delta =
      (w.p₀.delta.2,
        (g k (w.p₀.base.2 ^^^ w.p₀.delta.2) ^^^
          g k w.p₀.base.2) ^^^ w.p₀.delta.1) := by
    calc
      w.p₁.delta = (step k w.p₀).delta :=
        (congrArg (fun p : Point => p.delta) w.h₀).symm
      _ = _ := step_delta k w.p₀
  rw [hin] at hd
  change w.p₁.delta =
    (a.2, gDifference k w.p₁.base.1 a.2 ^^^ a.1)
  rw [← hb]
  exact hd

/-- Every left window over the fixed input difference is supported
at the graph point over its common base. -/
theorem left_at_graph (master : Master) (a : RoundState)
    (R : Point → Prop) (m : Point)
    (w : LeftAt master (inputDifference a) R m) :
    m = reconstructed master a m.base := by
  have hin : w.1.1.p₀.delta = a := w.1.2.1
  have hd := left_first_difference master a w.1.1 hin
  have hmid : w.1.1.p₁ = m := w.2
  have hdelta : m.delta = predictedDelta master a m.base := by
    simpa only [hmid] using hd
  exact (full_point_iff_base_and_difference m
    (reconstructed master a m.base)).mpr ⟨rfl, hdelta⟩

open scoped Classical in
/-- The fixed input differential forces the support of the actual
left weight onto a 64-bit graph, even when `a` is nonzero and the
middle predicate `R` is arbitrary. -/
theorem left_active_graph (master : Master) (a : RoundState)
    (R : Point → Prop) (m : Point)
    (h : 0 < leftWeight master (inputDifference a) R m) :
    m = reconstructed master a m.base := by
  classical
  change 0 < Fintype.card
    (LeftAt master (inputDifference a) R m) at h
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp h
  exact left_at_graph master a R m w

open scoped Classical in
/-- The exact left-right contraction is a sum over base states only.
It is NOT the product of independently aggregated weights under a
base-only observation: the right weight is evaluated at the unique
reconstructed full difference. -/
theorem fixed_input_exact_base_mass (master : Master)
    (a : RoundState) (Q R : Point → Prop) :
    Diffan.LabelJoinDefect.exactMass
        (leftWeight master (inputDifference a) R)
        (rightWeight master Q) =
      ∑ b : RoundState,
        leftWeight master (inputDifference a) R
          (reconstructed master a b) *
        rightWeight master Q (reconstructed master a b) := by
  classical
  unfold Diffan.LabelJoinDefect.exactMass
  apply Diffan.GraphSupportedJoin.sum_eq_graph_of_positive
    (fun m : Point => m.base)
    (reconstructed master a)
    (reconstructed_base master a)
    (leftWeight master (inputDifference a) R)
    (rightWeight master Q)
    (left_active_graph master a R)

open scoped Classical in
/-- Five real rounds, one master key, fixed (possibly nonzero) input
difference and arbitrary output/middle restrictions: exact counting
needs only a base-state index plus the reconstructed full point. -/
theorem five_count_fixed_input_by_base (master : Master)
    (a : RoundState) (Q R : Point → Prop) :
    Fintype.card (FiveRestricted master (inputDifference a) Q R) =
      ∑ b : RoundState,
        leftWeight master (inputDifference a) R
          (reconstructed master a b) *
        rightWeight master Q (reconstructed master a b) := by
  classical
  have hcount :
      Fintype.card (FiveRestricted master (inputDifference a) Q R) =
        Diffan.LabelJoinDefect.exactMass
          (leftWeight master (inputDifference a) R)
          (rightWeight master Q) := by
    calc
      _ = ∑ m : Point,
          conditionalMass master (inputDifference a) Q R m :=
        five_count_eq_conditional_mass master (inputDifference a) Q R
      _ = _ := rfl
  exact hcount.trans (fixed_input_exact_base_mass master a Q R)

open scoped Classical in
/-- Concrete family with NONZERO input and fully fixed output difference.
No promise of a positive count is made: the exact formula remains valid
for every fixed output difference, including impossible ones. -/
theorem nonzero_input_fixed_output_by_base (master : Master)
    (b : RoundState) (R : Point → Prop) :
    Fintype.card
        (FiveRestricted master
          (inputDifference ((1#32), (1#32)))
          (outputDifference b) R) =
      ∑ x : RoundState,
        leftWeight master
          (inputDifference ((1#32), (1#32))) R
          (reconstructed master ((1#32), (1#32)) x) *
        rightWeight master (outputDifference b)
          (reconstructed master ((1#32), (1#32)) x) := by
  exact five_count_fixed_input_by_base master ((1#32), (1#32))
    (outputDifference b) R

end Magma.DiffanFiveRoundFixedInputGraphJoin
