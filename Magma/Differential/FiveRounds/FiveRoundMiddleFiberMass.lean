module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundSinglePointOverlap

@[expose] public section

/-!
# Five-round middle-fiber mass: an exact weighted join

The one-point overlap theorem glues five real Magma rounds at one complete
StateDifference. This file decomposes that exact join into two conditional
window counts. The product is taken only AFTER fixing the entire common point.

An arbitrary finite observation can group these products into label fibers,
but summing the left and right marginals separately within one label is
NOT justified: the concrete common point must still match.
-/

namespace Magma.DifanFiveRoundMiddleFiberMass

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundOverlappingWindows
open Magma.DifanFiveRoundSinglePointOverlap

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Left four-round windows satisfying the input and middle predicates. -/
abbrev LeftEligible (master : Master) (P R : Point → Prop) : Type :=
  {a : FourWindow
      (roundKey master (0 : Fin 32))
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32)) //
    P a.p₀ ∧ R a.p₂}

/-- Right four-round windows satisfying the output predicate. -/
abbrev RightEligible (master : Master) (Q : Point → Prop) : Type :=
  {b : FourWindow
      (roundKey master (1 : Fin 32))
      (roundKey master (2 : Fin 32))
      (roundKey master (3 : Fin 32))
      (roundKey master (4 : Fin 32)) //
    Q b.p₄}

/-- Left windows ending at a fixed FULL first-common point. -/
abbrev LeftAt (master : Master) (P R : Point → Prop)
    (m : Point) : Type :=
  {a : LeftEligible master P R // a.1.p₁ = m}

/-- Right windows starting from the SAME fixed full point. -/
abbrev RightAt (master : Master) (Q : Point → Prop)
    (m : Point) : Type :=
  {b : RightEligible master Q // b.1.p₀ = m}

/-- The left and right conditional counts can be multiplied because they
share a complete middle point, not just a difference or projected label. -/
noncomputable def conditionalMass (master : Master) (P Q R : Point → Prop)
    (m : Point) : Nat :=
  by classical exact
    Fintype.card (LeftAt master P R m) *
      Fintype.card (RightAt master Q m)

/-- Decompose compatible windows by their complete common point,
retaining both conditional witnesses and the shared master key. -/
def restrictedMiddleSigmaEquiv (master : Master)
    (P Q R : Point → Prop) :
    FirstPointRestricted master P Q R ≃
      (Σ m : Point, LeftAt master P R m × RightAt master Q m) where
  toFun w :=
    ⟨w.1.1.1.p₁,
      (⟨⟨w.1.1.1, ⟨w.2.1, w.2.2.1⟩⟩, rfl⟩,
       ⟨⟨w.1.1.2, w.2.2.2⟩, w.1.2.symm⟩)⟩
  invFun w :=
    ⟨⟨(w.2.1.1.1, w.2.2.1.1),
        w.2.1.2.trans w.2.2.2.symm⟩,
      ⟨w.2.1.1.2.1, w.2.1.1.2.2, w.2.2.1.2⟩⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv := by
    intro w
    rcases w with ⟨m, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩
    cases ha
    rfl

/-- Exactly one genuine five-round path corresponds to each pair of
windows in the fixed-middle fiber. -/
def fiveMiddleSigmaEquiv (master : Master)
    (P Q R : Point → Prop) :
    FiveRestricted master P Q R ≃
      (Σ m : Point, LeftAt master P R m × RightAt master Q m) :=
  (scheduledRestrictedFirstEquiv master P Q R).trans
    (restrictedMiddleSigmaEquiv master P Q R)

open scoped Classical in
/-- The exact five-round path count is the contraction of two
*conditional* window masses over the complete middle StateDifference. -/
theorem five_count_eq_conditional_mass (master : Master)
    (P Q R : Point → Prop) :
    Fintype.card (FiveRestricted master P Q R) =
      ∑ m : Point, conditionalMass master P Q R m := by
  classical
  calc
    Fintype.card (FiveRestricted master P Q R) =
        Fintype.card
          (Σ m : Point, LeftAt master P R m × RightAt master Q m) :=
      Fintype.card_congr (fiveMiddleSigmaEquiv master P Q R)
    _ = ∑ m : Point, conditionalMass master P Q R m := by
      simp only [Fintype.card_sigma, Fintype.card_prod, conditionalMass]

open scoped Classical in
/-- An arbitrary finite observation groups the EXACT masses in its
fibers. A coarse observation never licenses multiplying its marginals. -/
theorem five_count_by_observation (master : Master)
    (P Q R : Point → Prop)
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (observe : Point → Label) :
    Fintype.card (FiveRestricted master P Q R) =
      ∑ label : Label,
        ∑ m : {m : Point // observe m = label},
          conditionalMass master P Q R m.1 := by
  classical
  rw [five_count_eq_conditional_mass]
  exact (Fintype.sum_fiberwise observe
    (conditionalMass master P Q R)).symm

/-- Equality of the full common StateDifference can be checked as
separate equality of its base and difference. -/
theorem full_point_iff_base_and_difference (a b : Point) :
    a = b ↔ a.base = b.base ∧ a.delta = b.delta := by
  constructor
  · intro h
    exact ⟨congrArg (fun x : Point => x.base) h,
      congrArg (fun x : Point => x.delta) h⟩
  · rintro ⟨hb, hd⟩
    cases a with
    | mk abase adelta =>
      cases b with
      | mk bbase bdelta =>
        dsimp at hb hd
        cases hb
        cases hd
        rfl

/-- Concrete lossless label reduction: when both candidate windows
already have the same complete difference at their common point,
only the base needs to be compared. Without that premise it is false. -/
theorem base_match_iff_full_of_same_delta
    {k₀ k₁ k₂ k₃ k₄ : Word}
    (a : FourWindow k₀ k₁ k₂ k₃)
    (b : FourWindow k₁ k₂ k₃ k₄)
    (hd : a.p₁.delta = b.p₀.delta) :
    a.p₁.base = b.p₀.base ↔ compatible a b := by
  rw [← first_shared_point_iff_compatible]
  exact ⟨fun hb =>
    (full_point_iff_base_and_difference a.p₁ b.p₀).2 ⟨hb, hd⟩,
    fun h => ((full_point_iff_base_and_difference a.p₁ b.p₀).1 h).1⟩

end Magma.DifanFiveRoundMiddleFiberMass
