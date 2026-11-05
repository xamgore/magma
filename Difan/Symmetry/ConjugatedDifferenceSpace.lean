module

public import Difan.Core.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.ConjugatedDifferenceSpace — transfer difference geometry through an equivalence

The DDT is not an invariant of arbitrary nonlinear conjugation when
the difference convention is held fixed. It IS invariant when the
difference structure is pulled back along the coordinate equivalence.

This applies to any DifferenceSpace, not only bitwise XOR.
No stochastic independence, factorization or finite-state approximation.
-/

namespace Difan.ConjugatedDifferenceSpace

variable {X Y Δ : Type*}

/-- Exact pulled-back difference geometry. Differences are measured
after applying e; shifts are carried back through e.inverse. -/
def pullback (e : X ≃ Y) (s : DifferenceSpace Y Δ) :
    DifferenceSpace X Δ where
  shift := fun x d => e.symm (s.shift (e x) d)
  diff := fun x y => s.diff (e x) (e y)
  shift_diff := by
    intro x y
    simp only [s.shift_diff, Equiv.symm_apply_apply]
  diff_shift := by
    intro x d
    simp only [Equiv.apply_symm_apply, s.diff_shift]

/-- Differences of a conjugated function are exactly the original
differences in transported coordinates, at the SAME base state e(x). -/
theorem derivative_conjugate (e : X ≃ Y) (s : DifferenceSpace Y Δ)
    (f : Y → Y) (a : Δ) (x : X) :
    derivative (pullback e s) (pullback e s)
      (e.symm ∘ f ∘ e) a x =
    derivative s s f a (e x) := by
  unfold derivative pullback
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

/-- Explicit bijection of real witness fibers for a nonlinear
change of state coordinates accompanied by the corresponding
change of difference geometry. -/
def conjugateFiberEquiv (e : X ≃ Y) (s : DifferenceSpace Y Δ)
    (f : Y → Y) (a b : Δ) :
    {x : X // derivative (pullback e s) (pullback e s)
      (e.symm ∘ f ∘ e) a x = b} ≃
    {y : Y // derivative s s f a y = b} where
  toFun := fun x =>
    ⟨e x.1, by
      have hx := x.2
      rw [derivative_conjugate] at hx
      exact hx⟩
  invFun := fun y =>
    ⟨e.symm y.1, by
      rw [derivative_conjugate, Equiv.apply_symm_apply]
      exact y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact e.apply_symm_apply y.1

/-- The general numerical DDT change-of-coordinates theorem,
for arbitrary finite types and any difference structure. -/
theorem ddt_conjugate [Fintype X] [Fintype Y] [DecidableEq Δ]
    (e : X ≃ Y) (s : DifferenceSpace Y Δ)
    (f : Y → Y) (a b : Δ) :
    ddt (pullback e s) (pullback e s)
      (e.symm ∘ f ∘ e) a b =
    ddt s s f a b := by
  classical
  unfold ddt
  calc
    ((Finset.univ : Finset X).filter (fun x =>
      derivative (pullback e s) (pullback e s)
        (e.symm ∘ f ∘ e) a x = b)).card =
        Fintype.card {x : X // derivative (pullback e s)
          (pullback e s) (e.symm ∘ f ∘ e) a x = b} := by
        simp only [Fintype.card_subtype]
    _ = Fintype.card {y : Y // derivative s s f a y = b} :=
      Fintype.card_congr (conjugateFiberEquiv e s f a b)
    _ = ((Finset.univ : Finset Y).filter (fun y =>
      derivative s s f a y = b)).card := by
        simp only [Fintype.card_subtype]

end Difan.ConjugatedDifferenceSpace
