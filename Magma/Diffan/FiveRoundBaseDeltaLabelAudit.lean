module

import all Init.Data.Range.Basic
public import Magma.Diffan.FiveRoundLabelJoinDefect
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Base-only and difference-only labels for five-round Magma windows

We compare two natural observations of the first common StateDifference of overlapping
four-round windows: the entire base and the entire difference.

Even for ONE fixed 256-bit master key, both observations admit genuine
false joins if endpoints are unrestricted. Explicit left and right
four-round windows witness these false joins.

For constrained windows we prove a positive result as well: exactness of
the base label is equivalent to agreement of the omitted difference on
all active cross-window pairs; dually for the difference label.
-/

namespace Magma.DiffanFiveRoundBaseDeltaLabelAudit

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundOverlappingWindows
open Magma.DiffanFiveRoundMiddleFiberMass
open Magma.DiffanFiveRoundLabelJoinDefect

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Completely unrestricted endpoint and middle predicates. -/
def unrestricted : Point → Prop := fun _ => True

def baseLabel (m : Point) : RoundState :=
  m.base

def deltaLabel (m : Point) : RoundState :=
  m.delta

/-- A real left four-round window can be started at any full point. -/
def leftFrom (master : Master) (p : Point) :
    FourWindow (roundKey master (0 : Fin 32))
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32)) := by
  let q₁ := step (roundKey master (0 : Fin 32)) p
  let q₂ := step (roundKey master (1 : Fin 32)) q₁
  let q₃ := step (roundKey master (2 : Fin 32)) q₂
  let q₄ := step (roundKey master (3 : Fin 32)) q₃
  exact ⟨p, q₁, q₂, q₃, q₄, rfl, rfl, rfl, rfl⟩

/-- An arbitrary full first-common point starts a genuine right window. -/
def rightFrom (master : Master) (m : Point) :
    FourWindow (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32))
      (roundKey master (4 : Fin 32)) := by
  let q₁ := step (roundKey master (1 : Fin 32)) m
  let q₂ := step (roundKey master (2 : Fin 32)) q₁
  let q₃ := step (roundKey master (3 : Fin 32)) q₂
  let q₄ := step (roundKey master (4 : Fin 32)) q₃
  exact ⟨m, q₁, q₂, q₃, q₄, rfl, rfl, rfl, rfl⟩

open scoped Classical in
/-- The left conditional mass is positive at this actual first-common point. -/
theorem left_weight_pos (master : Master) (p : Point) :
    0 < leftWeight master unrestricted unrestricted (leftFrom master p).p₁ := by
  classical
  change 0 < Fintype.card
    (LeftAt master unrestricted unrestricted (leftFrom master p).p₁)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨leftFrom master p, ⟨trivial, trivial⟩⟩, rfl⟩⟩

open scoped Classical in
/-- The right conditional mass is positive at EVERY full common point. -/
theorem right_weight_pos (master : Master) (m : Point) :
    0 < rightWeight master unrestricted m := by
  classical
  change 0 < Fintype.card (RightAt master unrestricted m)
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨rightFrom master m, trivial⟩, rfl⟩⟩

/-- Change the difference, keeping the entire base unchanged. -/
def deltaMate (m : Point) : Point :=
  ⟨m.base, (m.delta.1 ^^^ (1#32), m.delta.2)⟩

/-- Change the base, keeping the entire difference unchanged. -/
def baseMate (m : Point) : Point :=
  ⟨(m.base.1 ^^^ (1#32), m.base.2), m.delta⟩

@[simp]
theorem deltaMate_base (m : Point) : baseLabel (deltaMate m) = baseLabel m :=
  rfl

@[simp]
theorem baseMate_delta (m : Point) : deltaLabel (baseMate m) = deltaLabel m :=
  rfl

theorem deltaMate_ne (m : Point) : m ≠ deltaMate m := by
  have hword : m.delta.1 ≠ m.delta.1 ^^^ (1#32) := by bv_decide
  intro heq
  apply hword
  exact congrArg (fun p : Point => p.delta.1) heq

theorem baseMate_ne (m : Point) : m ≠ baseMate m := by
  have hword : m.base.1 ≠ m.base.1 ^^^ (1#32) := by bv_decide
  intro heq
  apply hword
  exact congrArg (fun p : Point => p.base.1) heq

open scoped Classical in
/-- A genuine active cross-pair with equal base but different differences. -/
theorem base_false_join (master : Master) :
    ∃ m n : Point,
      baseLabel m = baseLabel n ∧ m ≠ n ∧
      0 < leftWeight master unrestricted unrestricted m ∧
      0 < rightWeight master unrestricted n := by
  let p : Point := ⟨((0#32), (0#32)), ((0#32), (0#32))⟩
  let m := (leftFrom master p).p₁
  let n := deltaMate m
  refine ⟨m, n, ?_, deltaMate_ne m, ?_, ?_⟩
  · exact (deltaMate_base m).symm
  · exact left_weight_pos master p
  · exact right_weight_pos master n

open scoped Classical in
/-- A genuine active cross-pair with equal difference but different bases. -/
theorem delta_false_join (master : Master) :
    ∃ m n : Point,
      deltaLabel m = deltaLabel n ∧ m ≠ n ∧
      0 < leftWeight master unrestricted unrestricted m ∧
      0 < rightWeight master unrestricted n := by
  let p : Point := ⟨((0#32), (0#32)), ((0#32), (0#32))⟩
  let m := (leftFrom master p).p₁
  let n := baseMate m
  refine ⟨m, n, ?_, baseMate_ne m, ?_, ?_⟩
  · exact (baseMate_delta m).symm
  · exact left_weight_pos master p
  · exact right_weight_pos master n

open scoped Classical in
/-- An active false join contributes a positive off-diagonal weight
and therefore forces the label defect to be positive. -/
private theorem defect_pos_of_false_join
    (master : Master) (observe : Point → RoundState)
    (hex : ∃ m n : Point,
      observe m = observe n ∧ m ≠ n ∧
      0 < leftWeight master unrestricted unrestricted m ∧
      0 < rightWeight master unrestricted n) :
    0 < Diffan.LabelJoinDefect.defectMass observe
      (leftWeight master unrestricted unrestricted)
      (rightWeight master unrestricted) := by
  classical
  rcases hex with ⟨m, n, hlabel, hne, hL, hR⟩
  by_contra hnot
  have hz : Diffan.LabelJoinDefect.defectMass observe
      (leftWeight master unrestricted unrestricted)
      (rightWeight master unrestricted) = 0 := Nat.eq_zero_of_not_pos hnot
  have hzero :=
    (Diffan.LabelJoinDefect.defect_eq_zero_iff observe
      (leftWeight master unrestricted unrestricted)
      (rightWeight master unrestricted)).mp hz m n hlabel hne
  have hpos : 0 < leftWeight master unrestricted unrestricted m *
      rightWeight master unrestricted n := Nat.mul_pos hL hR
  omega

open scoped Classical in
/-- At every master key, forgetting the difference creates false joins. -/
theorem base_label_defect_pos (master : Master) :
    0 < Diffan.LabelJoinDefect.defectMass baseLabel
      (leftWeight master unrestricted unrestricted)
      (rightWeight master unrestricted) :=
  defect_pos_of_false_join master baseLabel (base_false_join master)

open scoped Classical in
/-- At every master key, forgetting the base also creates false joins. -/
theorem delta_label_defect_pos (master : Master) :
    0 < Diffan.LabelJoinDefect.defectMass deltaLabel
      (leftWeight master unrestricted unrestricted)
      (rightWeight master unrestricted) :=
  defect_pos_of_false_join master deltaLabel (delta_false_join master)

open scoped Classical in
/-- Every coarse count based only on the base strictly overcounts the
exact full-point contraction, for unrestricted genuine windows. -/
theorem base_coarse_strict (master : Master) :
    Diffan.LabelJoinDefect.exactMass
        (leftWeight master unrestricted unrestricted)
        (rightWeight master unrestricted) <
      Diffan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master unrestricted unrestricted)
        (rightWeight master unrestricted) := by
  have heq := Diffan.LabelJoinDefect.coarse_eq_exact_add_defect baseLabel
    (leftWeight master unrestricted unrestricted)
    (rightWeight master unrestricted)
  have hp := base_label_defect_pos master
  omega

open scoped Classical in
/-- The difference-only label also strictly overcounts. -/
theorem delta_coarse_strict (master : Master) :
    Diffan.LabelJoinDefect.exactMass
        (leftWeight master unrestricted unrestricted)
        (rightWeight master unrestricted) <
      Diffan.LabelJoinDefect.coarseMass deltaLabel
        (leftWeight master unrestricted unrestricted)
        (rightWeight master unrestricted) := by
  have heq := Diffan.LabelJoinDefect.coarse_eq_exact_add_defect deltaLabel
    (leftWeight master unrestricted unrestricted)
    (rightWeight master unrestricted)
  have hp := delta_label_defect_pos master
  omega

open scoped Classical in
/-- With arbitrary boundary conditions, the base-only label is exact iff
all active cross-window matches of bases already have equal differences. -/
theorem base_exact_iff_active_delta_agrees (master : Master)
    (P Q R : Point → Prop) :
    Diffan.LabelJoinDefect.coarseMass baseLabel
        (leftWeight master P R) (rightWeight master Q) =
      Diffan.LabelJoinDefect.exactMass
        (leftWeight master P R) (rightWeight master Q) ↔
      ∀ m n : Point, m.base = n.base →
        0 < leftWeight master P R m → 0 < rightWeight master Q n →
        m.delta = n.delta := by
  classical
  rw [Diffan.LabelJoinDefect.coarse_eq_exact_iff]
  constructor
  · intro h m n hb hL hR
    by_contra hd
    have hne : m ≠ n := by
      intro heq
      exact hd (congrArg (fun x : Point => x.delta) heq)
    have hz := h m n hb hne
    have hp : 0 < leftWeight master P R m * rightWeight master Q n :=
      Nat.mul_pos hL hR
    omega
  · intro h m n hb hne
    by_cases hL : 0 < leftWeight master P R m
    · by_cases hR : 0 < rightWeight master Q n
      · have heq : m = n :=
          (full_point_iff_base_and_difference m n).mpr ⟨hb, h m n hb hL hR⟩
        exact False.elim (hne heq)
      · have hz : rightWeight master Q n = 0 := Nat.eq_zero_of_not_pos hR
        simp [hz]
    · have hz : leftWeight master P R m = 0 := Nat.eq_zero_of_not_pos hL
      simp [hz]

open scoped Classical in
/-- Dually, the difference-only label is exact iff all active cross-window
matches of differences already have equal bases. -/
theorem delta_exact_iff_active_base_agrees (master : Master)
    (P Q R : Point → Prop) :
    Diffan.LabelJoinDefect.coarseMass deltaLabel
        (leftWeight master P R) (rightWeight master Q) =
      Diffan.LabelJoinDefect.exactMass
        (leftWeight master P R) (rightWeight master Q) ↔
      ∀ m n : Point, m.delta = n.delta →
        0 < leftWeight master P R m → 0 < rightWeight master Q n →
        m.base = n.base := by
  classical
  rw [Diffan.LabelJoinDefect.coarse_eq_exact_iff]
  constructor
  · intro h m n hd hL hR
    by_contra hb
    have hne : m ≠ n := by
      intro heq
      exact hb (congrArg (fun x : Point => x.base) heq)
    have hz := h m n hd hne
    have hp : 0 < leftWeight master P R m * rightWeight master Q n :=
      Nat.mul_pos hL hR
    omega
  · intro h m n hd hne
    by_cases hL : 0 < leftWeight master P R m
    · by_cases hR : 0 < rightWeight master Q n
      · have heq : m = n :=
          (full_point_iff_base_and_difference m n).mpr ⟨h m n hd hL hR, hd⟩
        exact False.elim (hne heq)
      · have hz : rightWeight master Q n = 0 := Nat.eq_zero_of_not_pos hR
        simp [hz]
    · have hz : leftWeight master P R m = 0 := Nat.eq_zero_of_not_pos hL
      simp [hz]

end Magma.DiffanFiveRoundBaseDeltaLabelAudit
