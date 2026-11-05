module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.CorrectionFiberSlices
public import Magma.Differential.Windows.ScheduledMeetFiberTransport
import Std.Tactic.BVDecide

@[expose] public section

/-!
# A correction fiber intersected with a true scheduled midpoint

`CorrectionFiberSlices` counts all possible right bases, with an optional
restriction. Here the restriction is not an independent DDT support: it is
induced by two endpoint predicates, an actual scheduled prefix and an actual
scheduled suffix, both executed with one 256-bit master key.

After fixing the left midpoint base, left midpoint difference, and right
midpoint difference, only the right midpoint base remains free. A conditional
correction slice counts precisely the right bases for which the corresponding
full `StateDifference` occurs in one joined trajectory and has correction b.

Endpoint predicates restrict the possible midpoints. The conditional count
is bounded by the corresponding unrestricted DDT coefficient.
All scheduled rounds here are ordinary G rounds, not the final GStar.
-/

namespace Magma.DiffanScheduledCorrectionReachability

open Magma
open Magma.CarryAutomaton
open Magma.DiffanFeistelDeltaPropagation
open Magma.DiffanCorrectionFiberSlices
open Magma.DiffanScheduledMeet
open scoped Classical

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Diffan.StateDifference (Word × Word) (Word × Word)

/-- A full midpoint with three fixed word coordinates and one variable
    *actual* right base coordinate. -/
def middleAt (L aL d R : Word) : Point :=
  ⟨(L, R), (aL, d)⟩

/-- Exact admissibility of that midpoint under a single scheduled master.
    P is imposed on the genuine initial pair; Q on the genuine final pair.
    The inverse prefix is essential: independently possible half paths are
    not silently identified with a concrete joined trajectory. -/
def admittedAt («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d R : Word) : Prop :=
  P ((leftEquiv «prefix» master).symm (middleAt L aL d R)) ∧
    Q (rightEquiv suffix master (middleAt L aL d R))

/-- Replace a midpoint's actual right base by the derivative base x=R XOR d.
    The filter is evaluated at x XOR d to recover R. -/
noncomputable def derivativeBaseFilter
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d : Word) : Word → Bool := by
  classical
  exact fun x => decide (admittedAt «prefix» suffix master P Q L aL d (x ^^^ d))

/-- The number of admissible concrete midpoints in the correction-b slice.
    `i` names the *actual scheduled key* used at the second-round correction. -/
noncomputable def scheduledCorrectionCount
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) : Nat :=
  correctionCountIf (roundKey master i) t d b
    (derivativeBaseFilter «prefix» suffix master P Q L aL d)

private theorem xor_twice (x d : Word) : (x ^^^ d) ^^^ d = x := by bv_decide

/-- The finite expression counts exactly the right bases whose *real*
    full midpoint satisfies both endpoint predicates and has correction b.
    This is the bridge to the `ScheduledMeet` semantics. -/
theorem scheduledCorrectionCount_spec
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b =
      ((Finset.univ : Finset Word).filter (fun R =>
        admittedAt «prefix» suffix master P Q L aL d R ∧
        secondCorrection (roundKey master i) t (middleAt L aL d R) = b)).card := by
  classical
  unfold scheduledCorrectionCount correctionCountIf derivativeBaseFilter
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, xor_twice]
  rfl

/-- A symbolic restricted derivative fiber: every counted x corresponds to
    one admissible real midpoint R=x XOR d. -/
theorem scheduledCorrectionCount_derivative
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b =
      derivativeCountIf (roundKey master i) t b
        (derivativeBaseFilter «prefix» suffix master P Q L aL d) := by
  exact correctionCountIf_eq_derivativeCountIf
    (roundKey master i) t d b
    (derivativeBaseFilter «prefix» suffix master P Q L aL d)

/-- Every admitted full midpoint really joins two scheduled endpoints.
    This uses the inverse of the actual prefix and the actual suffix,
    rather than matching two independently chosen abstract DDT paths. -/
theorem admittedAt_has_exact_meet
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d R : Word)
    (h : admittedAt «prefix» suffix master P Q L aL d R) :
    ∃ initial final : Point,
      P initial ∧ Q final ∧
      Diffan.Meet.meets (leftEquiv «prefix» master) (rightEquiv suffix master)
        initial final ∧
      leftEquiv «prefix» master initial = middleAt L aL d R := by
  refine ⟨(leftEquiv «prefix» master).symm (middleAt L aL d R),
    rightEquiv suffix master (middleAt L aL d R), h.1, h.2, ?_, ?_⟩
  · unfold Diffan.Meet.meets
    simp
  · simp

/-- A positive restricted correction coefficient has a concrete joined witness
    at the fixed middle left coordinates and right difference. -/
theorem positive_iff_admitted_midpoint
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    0 < scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b ↔
      ∃ R : Word,
        admittedAt «prefix» suffix master P Q L aL d R ∧
        secondCorrection (roundKey master i) t (middleAt L aL d R) = b := by
  rw [scheduledCorrectionCount_spec]
  constructor
  · intro h
    have hn : ((Finset.univ : Finset Word).filter (fun R =>
        admittedAt «prefix» suffix master P Q L aL d R ∧
        secondCorrection (roundKey master i) t (middleAt L aL d R) = b)).Nonempty :=
      Finset.card_pos.mp h
    rcases hn with ⟨R, hR⟩
    exact ⟨R, (Finset.mem_filter.mp hR).2⟩
  · rintro ⟨R, hR⟩
    apply Finset.card_pos.mpr
    exact ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ R, hR⟩⟩

/-- A scheduled correction slice is no larger than its unrestricted
    certified Magma XOR-DDT coefficient. No reachability assumption is lost. -/
theorem scheduledCorrectionCount_le_ddt
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b ≤
      xorDDT_g (roundKey master i) t b := by
  classical
  let Pder := derivativeBaseFilter «prefix» suffix master P Q L aL d
  have hsub :
      ((Finset.univ : Finset Word).filter (fun R =>
        Pder (R ^^^ d) = true ∧
          secondCorrection (roundKey master i) t (sampleMid R d) = b)) ⊆
      ((Finset.univ : Finset Word).filter (fun R =>
        (fun _ : Word => true) (R ^^^ d) = true ∧
          secondCorrection (roundKey master i) t (sampleMid R d) = b)) := by
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact hR.2
  have hle : correctionCountIf (roundKey master i) t d b Pder ≤
      correctionCountIf (roundKey master i) t d b (fun _ => true) := by
    unfold correctionCountIf
    exact Finset.card_le_card hsub
  change scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b ≤
    correctionCountIf (roundKey master i) t d b (fun _ => true) at hle
  simpa only [correctionCount_eq_xorDDT] using hle

/-- An impossible local DDT transition cannot reappear after restricting
    to an exact scheduled meet, regardless of the master-key schedule. -/
theorem scheduledCorrectionCount_zero_of_ddt_zero
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word)
    (hz : xorDDT_g (roundKey master i) t b = 0) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b = 0 := by
  exact Nat.eq_zero_of_le_zero (by
    simpa only [hz] using
      scheduledCorrectionCount_le_ddt «prefix» suffix master i P Q L aL d t b)

/-- For mask 0x6000, two specific right bases always produce different
    corrections at the same right difference, irrespective of the master.
    This says nothing yet about whether both pass endpoint restrictions. -/
theorem two_midpoint_corrections_distinct
    (master : Master) (i : Fin 32) (L aL d : Word) :
    secondCorrection (roundKey master i) (0x00006000#32)
        (middleAt L aL d ((0#32) ^^^ d)) ≠
      secondCorrection (roundKey master i) (0x00006000#32)
        (middleAt L aL d ((0x00001000#32) ^^^ d)) := by
  simpa only [secondCorrection, middleAt, midAt, sampleMid] using
    shift6000_distinct_on_each_right_difference (roundKey master i) d

/-- If both distinct witnesses pass the real prefix/suffix restrictions,
    the correction cannot be constant on the reachable midpoint slice.
    Conversely, a conditional constant correction requires excluding at
    least one of these two witnesses. -/
theorem two_admitted_midpoints_forbid_constant
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d b : Word)
    (h0 : admittedAt «prefix» suffix master P Q L aL d ((0#32) ^^^ d))
    (h1 : admittedAt «prefix» suffix master P Q L aL d
      ((0x00001000#32) ^^^ d)) :
    ¬ ∀ R : Word,
        admittedAt «prefix» suffix master P Q L aL d R →
          secondCorrection (roundKey master i) (0x00006000#32)
            (middleAt L aL d R) = b := by
  intro h
  exact two_midpoint_corrections_distinct master i L aL d
    ((h _ h0).trans (h _ h1).symm)

end Magma.DiffanScheduledCorrectionReachability
