module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundBaseDeltaLabelAudit

@[expose] public section

/-!
# A lossless base-only label on a genuine scheduled Magma slice

For overlapping windows, whether the base alone is a lossless label
depends on the boundary constraints:

* A zero input AND zero output difference makes `m.base` sufficient for
  exact gluing. The inner predicate R may be arbitrary.
* Fixing only the input difference, even to a nonzero word, is NOT enough
  when the right window remains unrestricted: a false cross-join exists
  under every master key.

These are statements about the actual five ordinary Feistel rounds,
with one scheduled 256-bit master key.
-/

namespace Magma.DiffanFiveRoundZeroBoundaryBaseLabel

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect
open Magma.DiffanFiveRoundBaseDeltaLabelAudit

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- The trivial difference of the full 64-bit Feistel state. -/
def zeroDifference : RoundState := ((0#32), (0#32))

def inputZero (p : Point) : Prop :=
  p.delta = zeroDifference

def outputZero (p : Point) : Prop :=
  p.delta = zeroDifference

def inputDifference (a : RoundState) (p : Point) : Prop :=
  p.delta = a

/-- One ordinary Feistel round has zero output difference exactly when
its input difference is zero. No assumption on the round key. -/
theorem step_zero_iff (k : Word) (p : Point) :
    (step k p).delta = zeroDifference ↔ p.delta = zeroDifference := by
  change (step k p).delta = ((0#32), (0#32)) ↔
    p.delta = ((0#32), (0#32))
  constructor
  · intro hout
    have hr : p.delta.2 = (0#32) := by
      calc
        p.delta.2 = (step k p).delta.1 := (step_left k p).symm
        _ = (0#32) := congrArg Prod.fst hout
    have hl : p.delta.1 = (0#32) := by
      calc
        p.delta.1 = (step k p).delta.2 :=
          (step_right_of_zero_right k p hr).symm
        _ = (0#32) := congrArg Prod.snd hout
    exact Prod.ext hl hr
  · intro hin
    have hl : p.delta.1 = (0#32) := congrArg Prod.fst hin
    have hr : p.delta.2 = (0#32) := congrArg Prod.snd hin
    exact Prod.ext ((step_left k p).trans hr)
      ((step_right_of_zero_right k p hr).trans hl)

/-- A valid left window started from a zero difference reaches its
first common point with zero difference. -/
theorem left_first_zero {k₀ k₁ k₂ k₃ : Word}
    (w : FourWindow k₀ k₁ k₂ k₃)
    (h : w.p₀.delta = zeroDifference) :
    w.p₁.delta = zeroDifference := by
  have hstep : (step k₀ w.p₀).delta = zeroDifference :=
    (step_zero_iff k₀ w.p₀).mpr h
  exact (congrArg (fun p : Point => p.delta) w.h₀).symm.trans hstep

/-- A valid right window with zero *final* difference must have
zero difference at its first point as well. -/
theorem right_first_zero {k₀ k₁ k₂ k₃ : Word}
    (w : FourWindow k₀ k₁ k₂ k₃)
    (h : w.p₄.delta = zeroDifference) :
    w.p₀.delta = zeroDifference := by
  have h₃ : w.p₃.delta = zeroDifference :=
    (step_zero_iff k₃ w.p₃).mp
      ((congrArg (fun p : Point => p.delta) w.h₃).trans h)
  have h₂ : w.p₂.delta = zeroDifference :=
    (step_zero_iff k₂ w.p₂).mp
      ((congrArg (fun p : Point => p.delta) w.h₂).trans h₃)
  have h₁ : w.p₁.delta = zeroDifference :=
    (step_zero_iff k₁ w.p₁).mp
      ((congrArg (fun p : Point => p.delta) w.h₁).trans h₂)
  exact (step_zero_iff k₀ w.p₀).mp
    ((congrArg (fun p : Point => p.delta) w.h₀).trans h₁)

open scoped Classical in
/-- Every active left weight with zero input difference is supported
at a zero-difference common point, regardless of the middle condition R. -/
theorem left_active_zero (master : Master) (R : Point → Prop)
    (m : Point)
    (h : 0 < leftWeight master inputZero R m) :
    m.delta = zeroDifference := by
  classical
  change 0 < Fintype.card (LeftAt master inputZero R m) at h
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp h
  have hstart : w.1.1.p₀.delta = zeroDifference := w.1.2.1
  have hfirst : w.1.1.p₁.delta = zeroDifference :=
    left_first_zero w.1.1 hstart
  exact (congrArg (fun p : Point => p.delta) w.2).symm.trans hfirst

open scoped Classical in
/-- The dual statement holds for every active right weight whose
output difference is zero. -/
theorem right_active_zero (master : Master) (m : Point)
    (h : 0 < rightWeight master outputZero m) :
    m.delta = zeroDifference := by
  classical
  change 0 < Fintype.card (RightAt master outputZero m) at h
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp h
  have hend : w.1.1.p₄.delta = zeroDifference := w.1.2
  have hfirst : w.1.1.p₀.delta = zeroDifference :=
    right_first_zero w.1.1 hend
  exact (congrArg (fun p : Point => p.delta) w.2).symm.trans hfirst

open scoped Classical in
/-- With zero boundary differences on both sides, checking the entire
base is enough because every active common point has zero difference.
Arbitrary middle restrictions R remain in force, as do all scheduled keys. -/
theorem zero_boundaries_base_exact (master : Master)
    (R : Point → Prop) :
    Diffan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master inputZero R)
        (rightWeight master outputZero) =
      Fintype.card (FiveRestricted master inputZero outputZero R) := by
  classical
  apply (five_coarse_exact_iff master inputZero outputZero R baseLabel).mpr
  intro m n hb hne
  by_cases hL : 0 < leftWeight master inputZero R m
  · by_cases hR : 0 < rightWeight master outputZero n
    · have hdelta : m.delta = n.delta :=
        (left_active_zero master R m hL).trans
          (right_active_zero master n hR).symm
      have hbase : m.base = n.base := hb
      have heq : m = n :=
        (full_point_iff_base_and_difference m n).mpr ⟨hbase, hdelta⟩
      exact False.elim (hne heq)
    · have hz : rightWeight master outputZero n = 0 :=
        Nat.eq_zero_of_not_pos hR
      simp [hz]
  · have hz : leftWeight master inputZero R m = 0 :=
      Nat.eq_zero_of_not_pos hL
    simp [hz]

open scoped Classical in
/-- Restricting just the left input difference (even fixing all 64 bits)
still leaves false base-label joins if the right window is unrestricted. -/
theorem fixed_input_only_base_defect_pos (master : Master)
    (a : RoundState) :
    0 < Diffan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master unrestricted) := by
  classical
  let p : Point := ⟨((0#32), (0#32)), a⟩
  let m : Point := (leftFrom master p).p₁
  let n : Point := deltaMate m
  have hlabel : baseLabel m = baseLabel n :=
    (deltaMate_base m).symm
  have hne : m ≠ n := deltaMate_ne m
  have hL : 0 < leftWeight master (inputDifference a) unrestricted m := by
    change 0 < Fintype.card
      (LeftAt master (inputDifference a) unrestricted m)
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨⟨leftFrom master p, ⟨rfl, trivial⟩⟩, rfl⟩⟩
  have hR : 0 < rightWeight master unrestricted n :=
    right_weight_pos master n
  by_contra hn
  have hz : Diffan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master unrestricted) = 0 := Nat.eq_zero_of_not_pos hn
  have hbad := (Diffan.LabelJoinDefect.defect_eq_zero_iff baseLabel
    (leftWeight master (inputDifference a) unrestricted)
    (rightWeight master unrestricted)).mp hz m n hlabel hne
  have hpositive : 0 <
      leftWeight master (inputDifference a) unrestricted m *
        rightWeight master unrestricted n := Nat.mul_pos hL hR
  omega

open scoped Classical in
/-- Thus the one-sided restriction still strictly overcounts genuine
five-round trajectories when joining merely by the common base. -/
theorem fixed_input_only_base_coarse_strict (master : Master)
    (a : RoundState) :
    Fintype.card
      (FiveRestricted master (inputDifference a) unrestricted unrestricted) <
    Diffan.LabelJoinDefect.coarseMass baseLabel
      (leftWeight master (inputDifference a) unrestricted)
      (rightWeight master unrestricted) := by
  have hmass := five_coarse_eq_real_plus_defect master
    (inputDifference a) unrestricted unrestricted baseLabel
  have hdefect := fixed_input_only_base_defect_pos master a
  omega

end Magma.DiffanFiveRoundZeroBoundaryBaseLabel
