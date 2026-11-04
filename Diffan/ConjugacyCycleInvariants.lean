module
public import Diffan.ConjugatedDifferenceSpace

@[expose] public section

/-!
# What nonlinear conjugacy REALLY preserves in the ordinary state space

For C=h^-1 o L o h, all periodic-point fibers of C and L are
bijective, hence the fixed-point counts of EVERY power coincide.
These are traces of powers of the Koopman permutation operator
and determine permutation cycle type. They are NOT individual
fixed-coordinate XOR LAT/Walsh entries; a concrete toy counterexample
is in Magma/Composition/transported_xor_spectral_probe.py.
-/

namespace Diffan.ConjugacyCycleInvariants

variable {X : Type*}

def conjugate (h : X ≃ X) (f : X → X) (x : X) : X :=
  h.symm (f (h x))

def power (f : X → X) : Nat → X → X
  | 0 => id
  | n+1 => fun x => f (power f n x)

/-- Every iterate of a conjugated permutation remains conjugate
to the corresponding iterate of the original function. -/
theorem power_conjugate (h : X ≃ X)
    (f : X → X) (n : Nat) (x : X) :
    h (power (conjugate h f) n x) = power f n (h x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change h (h.symm (f (h (power (conjugate h f) n x)))) =
      f (power f n (h x))
    rw [h.apply_symm_apply, ih]

/-- An exact bijection of the fixed points of EVERY power,
not just the ordinary fixed points n=1. -/
def periodicFiberEquiv (h : X ≃ X) (f : X → X) (n : Nat) :
    {x : X // power (conjugate h f) n x = x} ≃
    {u : X // power f n u = u} where
  toFun := fun p =>
    ⟨h p.1, by
      have hp := congrArg h p.2
      rw [power_conjugate] at hp
      exact hp⟩
  invFun := fun p =>
    ⟨h.symm p.1, by
      apply h.injective
      rw [power_conjugate, h.apply_symm_apply]
      exact p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact h.symm_apply_apply p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact h.apply_symm_apply p.1

/-- Exactly equal integer counts for arbitrary powers. These
are the power traces of the permutation Koopman operator.
They are universal conjugacy invariants and are NOT a
claim of efficient evaluation of those integer counts. -/
theorem periodic_counts_equal [Fintype X] [DecidableEq X]
    (h : X ≃ X) (f : X → X) (n : Nat) :
    Fintype.card {x : X // power (conjugate h f) n x = x} =
    Fintype.card {u : X // power f n u = u} := by
  exact Fintype.card_congr (periodicFiberEquiv h f n)

end Diffan.ConjugacyCycleInvariants
