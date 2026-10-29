module

public import Diffan.Differential
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Constraints — predicates and certified knowledge

A key condition is a *predicate*, not a list of keys. Intersections and
pullbacks work symbolically, without enumerating an enormous key space.
-/

namespace Diffan

/-- A symbolic family of keys. -/
abbrev KeyConstraint (K : Type*) := K → Prop

/-- Logical conjunction of two conditions on the same key. -/
def KeyConstraint.intersect {K : Type*}
    (p q : KeyConstraint K) : KeyConstraint K :=
  fun k => p k ∧ q k

/-- Transfer a round-key restriction back to the master-key space. -/
def KeyConstraint.pullback {M K : Type*}
    (roundKey : M → K) (p : KeyConstraint K) : KeyConstraint M :=
  fun master => p (roundKey master)

/-- The keys for which a given differential coefficient is nonzero. -/
def possibleKeys {K A B : Type*}
    (coeff : K → A → B → Nat) (a : A) (b : B) : KeyConstraint K :=
  fun k => coeff k a b > 0

/-- Keys attaining a specified value for a given transition. -/
def coefficientKeys {K A B : Type*}
    (coeff : K → A → B → Nat) (a : A) (b : B)
    (n : Nat) : KeyConstraint K :=
  fun k => coeff k a b = n

/-- A proved sharp upper bound for a selected transition. -/
structure SharpMaximum {K A B : Type*}
    (coeff : K → A → B → Nat) (t : Transition A B) where
  bound : Nat
  upper : ∀ k, coeff k t.input t.output ≤ bound
  witness : K
  attained : coeff witness t.input t.output = bound

/-- Constraints commute with pullback and intersection. -/
theorem KeyConstraint.pullback_intersect {M K : Type*}
    (f : M → K) (p q : KeyConstraint K) :
    KeyConstraint.pullback f (KeyConstraint.intersect p q) = KeyConstraint.intersect (KeyConstraint.pullback f p) (KeyConstraint.pullback f q) := by
  rfl

end Diffan
