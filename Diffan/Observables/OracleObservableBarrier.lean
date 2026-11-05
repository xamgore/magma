module
public import Diffan.Symmetry.BoomerangGauge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# A precise attack-model barrier for related-key gauge symmetries

The existence of a known state-change e intertwining
two key settings f and g, g(e x)=e(f x), places NO
restriction on the individual unknown permutation f
if g is available only as an *abstract second key*.

Indeed, for ANY f and ANY e, the family
  g := e o f o e^-1
satisfies this relation identically. Therefore this
relation alone cannot imply an impossible differential,
excess fixed points or standard single-key distinguishing
property for f. Extra constraints specific to real Magma
would be required.

The related-key model with oracles for both f and g is
different: its two-query relation is observable.
-/

namespace Diffan.OracleObservableBarrier

variable {X : Type*}

/-- The unique e-conjugate partner of ANY arbitrary
permutation, whether or not it is a secure cipher. -/
def partner (e f : X ≃ X) : X ≃ X :=
  (e.symm.trans f).trans e

theorem partner_apply (e f : X ≃ X) (x : X) :
    partner e f (e x) = e (f x) := by
  simp only [partner, Equiv.trans_apply, e.symm_apply_apply]

/-- No single-key restriction can follow from the
bare existential related-key gauge hypothesis:
EVERY possible bijection f has such a partner. -/
theorem every_permutation_has_gauge_partner
    (e f : X ≃ X) :
    ∃ g : X ≃ X, ∀ x, g (e x) = e (f x) := by
  exact ⟨partner e f, partner_apply e f⟩

/-- Uniqueness: the relation does specify g after f
is given. This does NOT give an oracle algorithm to
evaluate g when the partner key is inaccessible. -/
theorem gauge_partner_unique
    (e f g : X ≃ X)
    (hg : ∀ x, g (e x) = e (f x)) :
    g = partner e f := by
  ext y
  have h := hg (e.symm y)
  simpa only [e.apply_symm_apply, partner, Equiv.trans_apply,
    e.symm_apply_apply] using h

end Diffan.OracleObservableBarrier
