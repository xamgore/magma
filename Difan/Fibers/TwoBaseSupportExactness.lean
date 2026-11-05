module

import all Init.Data.Range.Basic
public import Difan.Fibers.ObservedGraphJoin

@[expose] public section

/-!
# An exact observation on two actively supported bases

A compressed observation need not distinguish *all* distinct points.
It is sufficient to distinguish the two reconstructed points at each
positively weighted base.  If all positive weight is confined to two
bases, one supporting a true join and the other a detected false join,
then the compressed count is already exact.

The support condition is essential: this theorem does NOT assert global
exactness of the observation.  It is independent of any cipher or DDT.
-/

namespace Difan.TwoBaseSupportExactness

variable {Base Middle Label : Type*}
variable [Fintype Base] [DecidableEq Middle] [DecidableEq Label]
open Difan.ObservedGraphJoin

/-- Two certified bases suffice for exactness on the chosen support.
The `good` base is fully compatible; the `bad` base is ruled out by the
short observation, even if its independently admissible windows have
positive weight. -/
theorem observed_exact_of_two_base_support
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) (good bad : Base)
    (hsupport : ∀ b : Base, 0 < weight b → b = good ∨ b = bad)
    (hgood : left good = right good)
    (hbad : observe (left bad) ≠ observe (right bad)) :
    observedMass observe left right weight = exactMass left right weight := by
  classical
  apply observed_exact_of_active_agreement observe left right weight
  intro b hb hobs
  rcases hsupport b hb with hg | hd
  · subst b
    exact hgood
  · subst b
    exact False.elim (hbad hobs)

/-- On two-base support, all false joins are observable, hence the
hidden mass vanishes. -/
theorem hidden_zero_of_two_base_support
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) (good bad : Base)
    (hsupport : ∀ b : Base, 0 < weight b → b = good ∨ b = bad)
    (hgood : left good = right good)
    (hbad : observe (left bad) ≠ observe (right bad)) :
    hiddenMass observe left right weight = 0 := by
  classical
  apply (observed_exact_iff_hidden_zero observe left right weight).mp
  exact observed_exact_of_two_base_support observe left right weight good bad
    hsupport hgood hbad

end Difan.TwoBaseSupportExactness
