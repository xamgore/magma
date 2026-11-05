module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledCorrectionReachability

@[expose] public section

/-!
# Conditional uniformity of the correction on genuinely reachable midpoints

The full midpoint is retained through the same scheduled 256-bit master key.
For three fixed midpoint coordinates, let `admittedBases` be the right base
values which truly connect a constrained prefix and suffix. This module
characterizes when one correction fiber occupies *all* of that admissible set.

The characterization is quantitative: the restricted correction count equals
the admissible midpoint count if and only if the correction is constant there.
It also gives exact vanishing outside the selected fiber, a genuine second
Feistel-round difference shift on admissible points, and a strict obstruction
when both previously certified witnesses are admitted.

-/

namespace Magma.DifanScheduledCorrectionHomogeneity

open Magma
open Magma.DifanFeistelDeltaPropagation
open Magma.DifanScheduledCorrectionReachability

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Difan.StateDifference (Word × Word) (Word × Word)

/-- Exactly those real right midpoint bases which meet both endpoint
    restrictions through the actual scheduled round functions. -/
noncomputable def admittedBases
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d : Word) : Finset Word := by
  classical
  exact (Finset.univ : Finset Word).filter
    (admittedAt «prefix» suffix master P Q L aL d)

@[simp]
theorem mem_admittedBases («prefix» suffix : List (Fin 32)) (master : Master) (P Q : Point → Prop)
    (L aL d R : Word) :
    R ∈ admittedBases «prefix» suffix master P Q L aL d ↔
      admittedAt «prefix» suffix master P Q L aL d R := by
  classical simp [admittedBases]

/-- Number of truly admissible right bases, before asking for a correction. -/
noncomputable def admittedMass
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q : Point → Prop) (L aL d : Word) : Nat :=
  (admittedBases «prefix» suffix master P Q L aL d).card

/-- Correction slices partition the admissible midpoint set by their
    correction value while retaining its endpoint restrictions. -/
theorem scheduledCount_as_filter
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b =
      ((admittedBases «prefix» suffix master P Q L aL d).filter
        (fun R => secondCorrection (roundKey master i) t
          (middleAt L aL d R) = b)).card := by
  classical
  rw [scheduledCorrectionCount_spec]
  simp only [admittedBases, Finset.filter_filter]

/-- The exact restricted correction count never exceeds the mass of
    genuinely admitted middle states (in addition to its known DDT bound). -/
theorem scheduledCount_le_admittedMass
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b ≤
      admittedMass «prefix» suffix master P Q L aL d := by
  classical
  rw [scheduledCount_as_filter]
  exact Finset.card_filter_le _ _

/-- A correction slice fills the complete admissible set if and only if
    every genuinely admitted middle base has that correction value.
    The equivalence remains valid if no midpoint is admitted. -/
theorem uniform_iff_full_mass
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b : Word) :
    (∀ R : Word,
      admittedAt «prefix» suffix master P Q L aL d R →
        secondCorrection (roundKey master i) t (middleAt L aL d R) = b) ↔
      scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b =
        admittedMass «prefix» suffix master P Q L aL d := by
  classical
  rw [scheduledCount_as_filter]
  unfold admittedMass
  rw [Finset.card_filter_eq_iff]
  simp only [mem_admittedBases]

/-- Under a conditional uniform correction, every other correction slice
    is empty. This is stronger than a mere DDT upper bound. -/
theorem other_slice_zero_of_uniform
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b b' : Word)
    (hu : ∀ R : Word,
      admittedAt «prefix» suffix master P Q L aL d R →
        secondCorrection (roundKey master i) t (middleAt L aL d R) = b)
    (hneq : b' ≠ b) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d t b' = 0 := by
  classical
  rw [scheduledCount_as_filter]
  have hfilter :
      (admittedBases «prefix» suffix master P Q L aL d).filter
        (fun R => secondCorrection (roundKey master i) t
          (middleAt L aL d R) = b') = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    rcases Finset.mem_filter.mp hR with ⟨hA, hB⟩
    exact hneq (hB.symm.trans (hu R ((mem_admittedBases «prefix» suffix master P Q L aL d R).mp hA)))
  rw [hfilter]
  rfl

/-- On the *actually admitted* midpoint set, full mass of one slice
    converts the state-dependent second-round propagation into a fixed
    shift of its two output difference words. -/
theorem admitted_second_round_uniform_shift
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d t b R : Word)
    (hfull : scheduledCorrectionCount «prefix» suffix master i P Q
        L aL d t b = admittedMass «prefix» suffix master P Q L aL d)
    (hR : admittedAt «prefix» suffix master P Q L aL d R) :
    roundPoint (roundKey master i)
        (shiftRightDelta t (middleAt L aL d R)) =
      ⟨(roundPoint (roundKey master i) (middleAt L aL d R)).base,
        ((roundPoint (roundKey master i) (middleAt L aL d R)).delta.1 ^^^ t,
         (roundPoint (roundKey master i) (middleAt L aL d R)).delta.2 ^^^ b)⟩ := by
  have hu := (uniform_iff_full_mass «prefix» suffix master i P Q
    L aL d t b).mpr hfull
  rw [second_round_shift, hu R hR]

/-- The two universal obstruction witnesses at direction 0x6000
    cannot both be present when any chosen correction slice is full. -/
theorem full_mass_excludes_two_witnesses
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d b : Word)
    (hfull : scheduledCorrectionCount «prefix» suffix master i P Q
      L aL d (0x00006000#32) b =
        admittedMass «prefix» suffix master P Q L aL d) :
    ¬ (admittedAt «prefix» suffix master P Q L aL d ((0#32) ^^^ d) ∧
        admittedAt «prefix» suffix master P Q L aL d ((0x00001000#32) ^^^ d)) := by
  intro hp
  have hu := (uniform_iff_full_mass «prefix» suffix master i P Q
    L aL d (0x00006000#32) b).mpr hfull
  exact two_admitted_midpoints_forbid_constant
    «prefix» suffix master i P Q L aL d b hp.1 hp.2 hu

/-- A genuinely quantitative obstruction: if both witnesses survive
    the prefix/suffix conditions, every individual correction slice
    occupies a proper subset of the admissible midpoint set. -/
theorem strict_count_of_two_admitted_witnesses
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d b : Word)
    (h0 : admittedAt «prefix» suffix master P Q L aL d ((0#32) ^^^ d))
    (h1 : admittedAt «prefix» suffix master P Q L aL d
      ((0x00001000#32) ^^^ d)) :
    scheduledCorrectionCount «prefix» suffix master i P Q L aL d
      (0x00006000#32) b < admittedMass «prefix» suffix master P Q L aL d := by
  have hle := scheduledCount_le_admittedMass «prefix» suffix master i
    P Q L aL d (0x00006000#32) b
  have hne : scheduledCorrectionCount «prefix» suffix master i P Q
      L aL d (0x00006000#32) b ≠ admittedMass «prefix» suffix master P Q L aL d := by
    intro hfull
    exact (full_mass_excludes_two_witnesses «prefix» suffix master i P Q
      L aL d b hfull) ⟨h0, h1⟩
  omega

/-- The same two admitted midpoints certify two distinct correction
    fibers of positive cardinality under one scheduled master key. -/
theorem two_positive_distinct_correction_slices
    («prefix» suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (P Q : Point → Prop) (L aL d : Word)
    (h0 : admittedAt «prefix» suffix master P Q L aL d ((0#32) ^^^ d))
    (h1 : admittedAt «prefix» suffix master P Q L aL d
      ((0x00001000#32) ^^^ d)) :
    ∃ b₀ b₁ : Word, b₀ ≠ b₁ ∧
      0 < scheduledCorrectionCount «prefix» suffix master i P Q L aL d
        (0x00006000#32) b₀ ∧
      0 < scheduledCorrectionCount «prefix» suffix master i P Q L aL d
        (0x00006000#32) b₁ := by
  let R₀ : Word := (0#32) ^^^ d
  let R₁ : Word := (0x00001000#32) ^^^ d
  let b₀ : Word := secondCorrection (roundKey master i) (0x00006000#32)
    (middleAt L aL d R₀)
  let b₁ : Word := secondCorrection (roundKey master i) (0x00006000#32)
    (middleAt L aL d R₁)
  have hneq : b₀ ≠ b₁ := two_midpoint_corrections_distinct master i L aL d
  refine ⟨b₀, b₁, hneq, ?_, ?_⟩
  · exact (positive_iff_admitted_midpoint «prefix» suffix master i P Q
      L aL d (0x00006000#32) b₀).mpr ⟨R₀, h0, rfl⟩
  · exact (positive_iff_admitted_midpoint «prefix» suffix master i P Q
      L aL d (0x00006000#32) b₁).mpr ⟨R₁, h1, rfl⟩

end Magma.DifanScheduledCorrectionHomogeneity
