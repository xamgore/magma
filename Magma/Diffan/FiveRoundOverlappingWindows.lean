module

import all Init.Data.Range.Basic
public import Magma.Diffan.FourRoundOneSidedBaseFiber

@[expose] public section

/-!
# Exact gluing of two overlapping four-round Magma windows

The five ordinary rounds 0--4, under a SINGLE 256-bit master key,
are viewed as windows [0,1,2,3] and [1,2,3,4].  They share four
COMPLETE StateDifference points (and therefore three transitions).

This module proves a bijection of real trajectory fibers, not a product
of marginal DDTs.  It is deliberately separate from the special
one-sided differential-equation reduction: an arbitrary five-round
path need not satisfy that reduction in either window.
-/

namespace Magma.DiffanFiveRoundOverlappingWindows

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFourRoundForcedMiddleDifference

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- One real four-step window, with all five full points retained. -/
structure FourWindow (k₀ k₁ k₂ k₃ : Word) where
  p₀ : Point
  p₁ : Point
  p₂ : Point
  p₃ : Point
  p₄ : Point
  h₀ : step k₀ p₀ = p₁
  h₁ : step k₁ p₁ = p₂
  h₂ : step k₂ p₂ = p₃
  h₃ : step k₃ p₃ = p₄

/-- A real five-step path, not a collection of independent DDT events. -/
structure FiveWindow (k₀ k₁ k₂ k₃ k₄ : Word) where
  p₀ : Point
  p₁ : Point
  p₂ : Point
  p₃ : Point
  p₄ : Point
  p₅ : Point
  h₀ : step k₀ p₀ = p₁
  h₁ : step k₁ p₁ = p₂
  h₂ : step k₂ p₂ = p₃
  h₃ : step k₃ p₃ = p₄
  h₄ : step k₄ p₄ = p₅

/-- Extensionality is by full points; transition proofs are propositions. -/
theorem fourWindow_eq_of_points {k₀ k₁ k₂ k₃ : Word}
    (a b : FourWindow k₀ k₁ k₂ k₃)
    (h₀ : a.p₀ = b.p₀) (h₁ : a.p₁ = b.p₁)
    (h₂ : a.p₂ = b.p₂) (h₃ : a.p₃ = b.p₃)
    (h₄ : a.p₄ = b.p₄) : a = b := by
  cases a with
  | mk a₀ a₁ a₂ a₃ a₄ ha₀ ha₁ ha₂ ha₃ =>
    cases b with
    | mk b₀ b₁ b₂ b₃ b₄ hb₀ hb₁ hb₂ hb₃ =>
      dsimp at h₀ h₁ h₂ h₃ h₄
      subst b₀
      subst b₁
      subst b₂
      subst b₃
      subst b₄
      rfl

/-- First four steps, including the actual states in their common part. -/
def FiveWindow.first {k₀ k₁ k₂ k₃ k₄ : Word}
    (w : FiveWindow k₀ k₁ k₂ k₃ k₄) : FourWindow k₀ k₁ k₂ k₃ :=
  ⟨w.p₀, w.p₁, w.p₂, w.p₃, w.p₄, w.h₀, w.h₁, w.h₂, w.h₃⟩

/-- Last four steps, with the SAME keys on the three shared rounds. -/
def FiveWindow.last {k₀ k₁ k₂ k₃ k₄ : Word}
    (w : FiveWindow k₀ k₁ k₂ k₃ k₄) : FourWindow k₁ k₂ k₃ k₄ :=
  ⟨w.p₁, w.p₂, w.p₃, w.p₄, w.p₅, w.h₁, w.h₂, w.h₃, w.h₄⟩

/-- All four full overlap points must agree, not only their differences. -/
def compatible {k₀ k₁ k₂ k₃ k₄ : Word}
    (a : FourWindow k₀ k₁ k₂ k₃)
    (b : FourWindow k₁ k₂ k₃ k₄) : Prop :=
  a.p₁ = b.p₀ ∧ a.p₂ = b.p₁ ∧ a.p₃ = b.p₂ ∧ a.p₄ = b.p₃

/-- Fiber of compatible pairs of overlapping four-round windows. -/
abbrev Overlap (k₀ k₁ k₂ k₃ k₄ : Word) : Type :=
  {ab : FourWindow k₀ k₁ k₂ k₃ × FourWindow k₁ k₂ k₃ k₄ //
    compatible ab.1 ab.2}

/-- Restrict a five-round execution to the two overlapping windows. -/
def toOverlap {k₀ k₁ k₂ k₃ k₄ : Word}
    (w : FiveWindow k₀ k₁ k₂ k₃ k₄) : Overlap k₀ k₁ k₂ k₃ k₄ :=
  ⟨(w.first, w.last), ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Glue a compatible pair without counting any shared transition twice. -/
def fromOverlap {k₀ k₁ k₂ k₃ k₄ : Word}
    (ab : Overlap k₀ k₁ k₂ k₃ k₄) : FiveWindow k₀ k₁ k₂ k₃ k₄ := by
  let a := ab.1.1
  let b := ab.1.2
  have hshared : a.p₄ = b.p₃ := ab.2.2.2.2
  exact ⟨a.p₀, a.p₁, a.p₂, a.p₃, a.p₄, b.p₄,
    a.h₀, a.h₁, a.h₂, a.h₃, by rw [hshared]; exact b.h₃⟩

/-- A real five-step path is recovered from its two overlapping windows. -/
theorem fromOverlap_toOverlap {k₀ k₁ k₂ k₃ k₄ : Word}
    (w : FiveWindow k₀ k₁ k₂ k₃ k₄) :
    fromOverlap (toOverlap w) = w := by
  cases w
  rfl

/-- Two compatible four-step windows are recovered from their glued path. -/
theorem toOverlap_fromOverlap {k₀ k₁ k₂ k₃ k₄ : Word}
    (ab : Overlap k₀ k₁ k₂ k₃ k₄) :
    toOverlap (fromOverlap ab) = ab := by
  rcases ab with ⟨⟨a, b⟩, ⟨h₁, h₂, h₃, h₄⟩⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply fourWindow_eq_of_points
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
    · rfl

/-- Exact window-gluing certificate for arbitrary round keys. -/
def fiveOverlapEquiv (k₀ k₁ k₂ k₃ k₄ : Word) :
    FiveWindow k₀ k₁ k₂ k₃ k₄ ≃ Overlap k₀ k₁ k₂ k₃ k₄ where
  toFun := toOverlap
  invFun := fromOverlap
  left_inv := fromOverlap_toOverlap
  right_inv := toOverlap_fromOverlap

/-- With deterministic round transitions, a window is uniquely determined
by its initial full point, so finiteness of the point space gives
finiteness of the window space. -/
theorem fourWindow_start_injective (k₀ k₁ k₂ k₃ : Word) :
    Function.Injective (fun w : FourWindow k₀ k₁ k₂ k₃ => w.p₀) := by
  intro a b h₀
  have h₁ : a.p₁ = b.p₁ := by
    calc
      a.p₁ = step k₀ a.p₀ := a.h₀.symm
      _ = step k₀ b.p₀ := congrArg (step k₀) h₀
      _ = b.p₁ := b.h₀
  have h₂ : a.p₂ = b.p₂ := by
    calc
      a.p₂ = step k₁ a.p₁ := a.h₁.symm
      _ = step k₁ b.p₁ := congrArg (step k₁) h₁
      _ = b.p₂ := b.h₁
  have h₃ : a.p₃ = b.p₃ := by
    calc
      a.p₃ = step k₂ a.p₂ := a.h₂.symm
      _ = step k₂ b.p₂ := congrArg (step k₂) h₂
      _ = b.p₃ := b.h₂
  have h₄ : a.p₄ = b.p₄ := by
    calc
      a.p₄ = step k₃ a.p₃ := a.h₃.symm
      _ = step k₃ b.p₃ := congrArg (step k₃) h₃
      _ = b.p₄ := b.h₃
  exact fourWindow_eq_of_points a b h₀ h₁ h₂ h₃ h₄

instance fourWindow_finite (k₀ k₁ k₂ k₃ : Word) : Finite (FourWindow k₀ k₁ k₂ k₃) :=
  Finite.of_injective _ (fourWindow_start_injective k₀ k₁ k₂ k₃)

/-- A non-executable finite enumerator, used only for cardinality theorems. -/
noncomputable instance fourWindow_fintype (k₀ k₁ k₂ k₃ : Word) :
    Fintype (FourWindow k₀ k₁ k₂ k₃) := Fintype.ofFinite _

instance fiveWindow_finite (k₀ k₁ k₂ k₃ k₄ : Word) : Finite (FiveWindow k₀ k₁ k₂ k₃ k₄) := by
  apply Finite.of_injective (toOverlap : FiveWindow k₀ k₁ k₂ k₃ k₄ → Overlap k₀ k₁ k₂ k₃ k₄)
  intro a b h
  calc
    a = fromOverlap (toOverlap a) := (fromOverlap_toOverlap a).symm
    _ = fromOverlap (toOverlap b) := congrArg (fun w : Overlap k₀ k₁ k₂ k₃ k₄ => fromOverlap w) h
    _ = b := fromOverlap_toOverlap b

noncomputable instance fiveWindow_fintype (k₀ k₁ k₂ k₃ k₄ : Word) :
    Fintype (FiveWindow k₀ k₁ k₂ k₃ k₄) :=
  Fintype.ofFinite _

/-- Specialization uses five subkeys of ONE genuine Magma master key. -/
abbrev ScheduledFive (master : Master) : Type :=
  FiveWindow (roundKey master (0 : Fin 32))
    (roundKey master (1 : Fin 32))
    (roundKey master (2 : Fin 32))
    (roundKey master (3 : Fin 32))
    (roundKey master (4 : Fin 32))

abbrev ScheduledOverlap (master : Master) : Type :=
  Overlap (roundKey master (0 : Fin 32)) (roundKey master (1 : Fin 32))
    (roundKey master (2 : Fin 32)) (roundKey master (3 : Fin 32)) (roundKey master (4 : Fin 32))

/-- Gluing preserves the common master key and the full shared trajectory. -/
def scheduledOverlapEquiv (master : Master) :
    ScheduledFive master ≃ ScheduledOverlap master :=
  fiveOverlapEquiv _ _ _ _ _

/-- Shared points include both the actual base and the difference. -/
theorem scheduled_shared_middle (master : Master)
    (w : ScheduledOverlap master) :
    w.1.1.p₂.base = w.1.2.p₁.base ∧
    w.1.1.p₂.delta = w.1.2.p₁.delta := by
  exact ⟨congrArg (fun p : Point => p.base) w.2.2.1,
    congrArg (fun p : Point => p.delta) w.2.2.1⟩

/-- A mismatch of any observation of the shared full point rejects a
window pair. Agreement of observations is only a necessary condition. -/
theorem observation_mismatch_excludes_gluing
    {k₀ k₁ k₂ k₃ k₄ : Word} {Label : Type*}
    (a : FourWindow k₀ k₁ k₂ k₃)
    (b : FourWindow k₁ k₂ k₃ k₄)
    (observe : Point → Label)
    (h : observe a.p₂ ≠ observe b.p₁) : ¬ compatible a b := by
  intro hc
  exact h (congrArg observe hc.2.1)

/-- Restrict both endpoints and one complete interior StateDifference. -/
abbrev FiveRestricted (master : Master) (P Q R : Point → Prop) : Type :=
  {w : ScheduledFive master // P w.p₀ ∧ R w.p₂ ∧ Q w.p₅}

/-- All three restrictions, now on compatible windows. -/
abbrev OverlapRestricted (master : Master) (P Q R : Point → Prop) : Type :=
  {w : ScheduledOverlap master // P w.1.1.p₀ ∧ R w.1.1.p₂ ∧ Q w.1.2.p₄}

/-- Endpoint restrictions survive gluing exactly. -/
def scheduledRestrictedEquiv (master : Master) (P Q R : Point → Prop) :
    FiveRestricted master P Q R ≃ OverlapRestricted master P Q R where
  toFun w := ⟨scheduledOverlapEquiv master w.1, w.2⟩
  invFun w := ⟨(scheduledOverlapEquiv master).symm w.1, w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (scheduledOverlapEquiv master).symm_apply_apply w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact (scheduledOverlapEquiv master).apply_symm_apply w.1

open scoped Classical in
/-- Exact cardinality of a five-round endpoint fiber, obtained by
joining compatible overlapping windows. Independent DDT products do not
appear; each matched pair represents exactly one real execution. -/
theorem scheduled_restricted_count (master : Master) (P Q R : Point → Prop) :
    Fintype.card (FiveRestricted master P Q R) =
      Fintype.card (OverlapRestricted master P Q R) := by
  classical
  exact Fintype.card_congr (scheduledRestrictedEquiv master P Q R)

end Magma.DiffanFiveRoundOverlappingWindows
