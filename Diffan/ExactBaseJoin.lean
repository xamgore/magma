module
public import Diffan.StateDifference
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact conditional base join, without multiplying marginal DDTs

For f bijective and g arbitrary, an intermediate BASE y=f(x)
is a sufficient join label for the f;g differential experiment.
The intermediate difference mu is NOT an independent choice:
mu = derivative f a (f^-1 y).

The exact Nat count is a single sum over y of the deterministic
conditional predicate on the SAME base y. This is compatible
with any DifferenceSpace; it does NOT assert computational
tractability when X has 2^64 elements.

For Magma, apply with f=H^2 (16 normal rounds) and
g=Q16=J E16 (the reflected 16-round macro including final
no-swap convention). The outside input/output can be any
64-bit XOR differences, including (a,0) and (0,b).
-/

namespace Diffan.ExactBaseJoin

variable {X Δ : Type*}

/-- The actual intermediate derivative after f, indexed by
the genuine intermediate base y=f(x), not by a DDT marginal. -/
def intermediateDelta
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (a : Δ) (y : X) : Δ :=
  derivative s s f a (f.symm y)

/-- The EXACT state-labelled path count for f then g.
No fake Markov independence and no summation over mu. -/
def count [Fintype X] [DecidableEq Δ]
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (g : X → X) (a b : Δ) : Nat :=
  ((Finset.univ : Finset X).filter (fun y =>
    derivative s s g (intermediateDelta s f a y) y = b)).card

/-- A bijection of ACTUAL base witnesses at the join. -/
def witnessEquiv
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (g : X → X) (a b : Δ) :
    {x : X // derivative s s (g ∘ f) a x = b} ≃
    {y : X // derivative s s g (intermediateDelta s f a y) y = b} where
  toFun := fun p =>
    ⟨f p.1, by
      have h := p.2
      rw [derivative_comp s s s f g a p.1] at h
      simpa only [intermediateDelta, f.symm_apply_apply] using h⟩
  invFun := fun p =>
    ⟨f.symm p.1, by
      have h := p.2
      rw [derivative_comp s s s f g a]
      simpa only [intermediateDelta, f.apply_symm_apply] using h⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact f.symm_apply_apply p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact f.apply_symm_apply p.1

/-- Main exact join law: the joint intermediate base and
difference are correctly correlated, so this is an
equality of natural DDT counts for EVERY f,g,a,b. -/
theorem ddt_comp_eq_exactBaseJoin
    [Fintype X] [DecidableEq Δ]
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (g : X → X) (a b : Δ) :
    ddt s s (g ∘ f) a b = count s f g a b := by
  classical
  unfold ddt count
  calc
    ((Finset.univ : Finset X).filter (fun x =>
      derivative s s (g ∘ f) a x = b)).card =
      Fintype.card {x : X // derivative s s (g ∘ f) a x = b} := by
        simp only [Fintype.card_subtype]
    _ = Fintype.card {y : X //
         derivative s s g (intermediateDelta s f a y) y = b} :=
      Fintype.card_congr (witnessEquiv s f g a b)
    _ = ((Finset.univ : Finset X).filter (fun y =>
      derivative s s g (intermediateDelta s f a y) y = b)).card := by
        simp only [Fintype.card_subtype]

/-- A selected intermediate difference mu is realized by
ONE actual y only if it equals its functional derivative. -/
def conditionalAt
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (a mu : Δ) (y : X) : Prop :=
  intermediateDelta s f a y = mu

/-- With a bijective prefix, all intermediate difference
labels mu can be eliminated purely FUNCTIONALLY, leaving
the base y as the only join variable. -/
theorem exists_mu_eliminates
    (s : DifferenceSpace X Δ) (f : X ≃ X)
    (g : X → X) (a b : Δ) (y : X) :
    (∃ mu : Δ, conditionalAt s f a mu y ∧
      derivative s s g mu y = b) ↔
      derivative s s g (intermediateDelta s f a y) y = b := by
  constructor
  · rintro ⟨mu, hm, hg⟩
    change intermediateDelta s f a y = mu at hm
    rw [hm]
    exact hg
  · intro h
    exact ⟨intermediateDelta s f a y, rfl, h⟩

end Diffan.ExactBaseJoin
