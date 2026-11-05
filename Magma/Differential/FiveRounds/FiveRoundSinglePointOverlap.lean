module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundOverlappingWindows

@[expose] public section

/-!
# One full common point is enough to glue overlapping Magma windows

A pair of *valid* four-round windows [0,1,2,3] and [1,2,3,4]
shares three deterministic transitions. Equality of their FIRST common
StateDifference therefore forces equality at the other three common
points. No additional DDT or key-independence hypothesis is needed.

This is a lossless simplification of the established five-round overlap
certificate. The windows themselves still contain actual full states:
matching only their differences, or matching arbitrary partial labels,
is NOT sufficient.
-/

namespace Magma.DiffanFiveRoundSinglePointOverlap

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFiveRoundOverlappingWindows

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Determinism of the three SHARED rounds means that the first common
complete point determines the entire common portion of both windows. -/
theorem first_shared_point_iff_compatible
    {k₀ k₁ k₂ k₃ k₄ : Word}
    (a : FourWindow k₀ k₁ k₂ k₃)
    (b : FourWindow k₁ k₂ k₃ k₄) :
    a.p₁ = b.p₀ ↔ compatible a b := by
  constructor
  · intro h₁
    have h₂ : a.p₂ = b.p₁ := by
      calc
        a.p₂ = step k₁ a.p₁ := a.h₁.symm
        _ = step k₁ b.p₀ := congrArg (step k₁) h₁
        _ = b.p₁ := b.h₀
    have h₃ : a.p₃ = b.p₂ := by
      calc
        a.p₃ = step k₂ a.p₂ := a.h₂.symm
        _ = step k₂ b.p₁ := congrArg (step k₂) h₂
        _ = b.p₂ := b.h₁
    have h₄ : a.p₄ = b.p₃ := by
      calc
        a.p₄ = step k₃ a.p₃ := a.h₃.symm
        _ = step k₃ b.p₂ := congrArg (step k₃) h₃
        _ = b.p₃ := b.h₂
    exact ⟨h₁, h₂, h₃, h₄⟩
  · intro h
    exact h.1

/-- A minimal overlap certificate: only one COMPLETE point is matched.
The other three matches are consequences, not separate assumptions. -/
abbrev FirstPointOverlap (k₀ k₁ k₂ k₃ k₄ : Word) : Type :=
  {ab : FourWindow k₀ k₁ k₂ k₃ × FourWindow k₁ k₂ k₃ k₄ //
    ab.1.p₁ = ab.2.p₀}

/-- Matching all four common points and matching the first common point
select the same pairs of valid windows. -/
def overlapFirstPointEquiv (k₀ k₁ k₂ k₃ k₄ : Word) :
    Overlap k₀ k₁ k₂ k₃ k₄ ≃
      FirstPointOverlap k₀ k₁ k₂ k₃ k₄ where
  toFun w := ⟨w.1, w.2.1⟩
  invFun w := ⟨w.1,
    (first_shared_point_iff_compatible w.1.1 w.1.2).mp w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- Genuine five-round execution and one-point-compatible window pairs
are in exact bijection for arbitrary (but shared) round keys. -/
def fiveFirstPointEquiv (k₀ k₁ k₂ k₃ k₄ : Word) :
    FiveWindow k₀ k₁ k₂ k₃ k₄ ≃
      FirstPointOverlap k₀ k₁ k₂ k₃ k₄ :=
  (fiveOverlapEquiv k₀ k₁ k₂ k₃ k₄).trans
    (overlapFirstPointEquiv k₀ k₁ k₂ k₃ k₄)

/-- Same five keys, all obtained from one 256-bit master key. -/
abbrev ScheduledFirstPointOverlap (master : Master) : Type :=
  FirstPointOverlap (roundKey master (0 : Fin 32))
    (roundKey master (1 : Fin 32))
    (roundKey master (2 : Fin 32))
    (roundKey master (3 : Fin 32))
    (roundKey master (4 : Fin 32))

/-- Scheduled full paths can be glued by checking a single full
StateDifference at the beginning of the common part. -/
def scheduledFirstPointEquiv (master : Master) :
    ScheduledFive master ≃ ScheduledFirstPointOverlap master :=
  fiveFirstPointEquiv _ _ _ _ _

/-- Retain arbitrary conditions at the initial point, shared middle,
and final point; these need not factor across the two windows. -/
abbrev FirstPointRestricted (master : Master)
    (P Q R : Point → Prop) : Type :=
  {ab : ScheduledFirstPointOverlap master //
    P ab.1.1.p₀ ∧ R ab.1.1.p₂ ∧ Q ab.1.2.p₄}

/-- Endpoint and interior conditions refer to the same full points
under either overlap predicate. -/
def restrictedOverlapFirstEquiv (master : Master)
    (P Q R : Point → Prop) :
    OverlapRestricted master P Q R ≃
      FirstPointRestricted master P Q R where
  toFun w :=
    ⟨overlapFirstPointEquiv _ _ _ _ _ w.1, w.2⟩
  invFun w :=
    ⟨(overlapFirstPointEquiv _ _ _ _ _).symm w.1, w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (overlapFirstPointEquiv _ _ _ _ _).symm_apply_apply w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact (overlapFirstPointEquiv _ _ _ _ _).apply_symm_apply w.1

/-- A restricted five-round path corresponds to a pair of windows
with the same first common point and the same point restrictions. -/
def scheduledRestrictedFirstEquiv (master : Master)
    (P Q R : Point → Prop) :
    FiveRestricted master P Q R ≃
      FirstPointRestricted master P Q R :=
  (scheduledRestrictedEquiv master P Q R).trans
    (restrictedOverlapFirstEquiv master P Q R)

open scoped Classical in
/-- Exact quantitative statement: one common full point suffices for
counting compatible window pairs without overcounting any shared path. -/
theorem scheduled_one_point_count (master : Master)
    (P Q R : Point → Prop) :
    Fintype.card (FiveRestricted master P Q R) =
      Fintype.card (FirstPointRestricted master P Q R) := by
  classical
  exact Fintype.card_congr
    (scheduledRestrictedFirstEquiv master P Q R)

/-- An observable mismatch at the first common point rules out gluing.
Equal *partial* labels alone are not asserted to be sufficient. -/
theorem first_observation_mismatch_excludes
    {k₀ k₁ k₂ k₃ k₄ : Word} {Label : Type*}
    (a : FourWindow k₀ k₁ k₂ k₃)
    (b : FourWindow k₁ k₂ k₃ k₄)
    (observe : Point → Label)
    (hmismatch : observe a.p₁ ≠ observe b.p₀) :
    ¬ compatible a b := by
  intro hc
  exact hmismatch (congrArg observe hc.1)

end Magma.DiffanFiveRoundSinglePointOverlap
