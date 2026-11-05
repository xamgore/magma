module

import all Init.Data.Range.Basic
public import Diffan.Core.InverseDDT
public import Diffan.Paths.Chain

@[expose] public section

/-!
# Reversible chains

A `ReversibleChain X` contains a chronological forward chain, a
chronological inverse chain, and the proofs that they cancel. Its
`append` executes `c`, then `d`, while the inverse executes the inverse
of `d`, then the inverse of `c`.

This is a proof-carrying object, unlike a bare `Chain X`, which need not
be invertible. It does NOT assume round functions are statistically
independent or that individual DDT probabilities multiply.
-/

namespace Diffan

/-- A chain with a certified inverse in the same state space. -/
structure ReversibleChain (X : Type*) where
  forward : Chain X
  backward : Chain X
  backward_forward : ∀ x, backward.run (forward.run x) = x
  forward_backward : ∀ x, forward.run (backward.run x) = x

namespace ReversibleChain

/-- The empty reversible chain. -/
def nil {X : Type*} : ReversibleChain X where
  forward := Chain.nil
  backward := Chain.nil
  backward_forward := by intro x; rfl
  forward_backward := by intro x; rfl

/-- Interpret one equivalence as a one-step reversible chain. -/
def single {X : Type*} (f : X ≃ X) : ReversibleChain X where
  forward := Chain.cons (fun x => f x) Chain.nil
  backward := Chain.cons (fun y => f.symm y) Chain.nil
  backward_forward := by
    intro x
    simpa only [Chain.run_cons, Chain.run_nil] using f.symm_apply_apply x
  forward_backward := by
    intro x
    simpa only [Chain.run_cons, Chain.run_nil] using f.apply_symm_apply x

/-- Execute `c` followed by `d`; reverse execution runs in reverse order. -/
def append {X : Type*} (c d : ReversibleChain X) : ReversibleChain X where
  forward := c.forward.append d.forward
  backward := d.backward.append c.backward
  backward_forward := by
    intro x
    simp only [Chain.run_append]
    rw [d.backward_forward, c.backward_forward]
  forward_backward := by
    intro x
    simp only [Chain.run_append]
    rw [c.forward_backward, d.forward_backward]

/-- Exchange the forward and reverse chains. -/
def reverse {X : Type*} (c : ReversibleChain X) : ReversibleChain X where
  forward := c.backward
  backward := c.forward
  backward_forward := c.forward_backward
  forward_backward := c.backward_forward

/-- A list of invertible transformations, executed in listed order. -/
def fromSteps {X : Type*} : List (X ≃ X) → ReversibleChain X
  | [] => nil
  | f :: fs => (single f).append (fromSteps fs)

@[simp]
theorem fromSteps_nil {X : Type*} : fromSteps ([] : List (X ≃ X)) = nil :=
  rfl

@[simp]
theorem fromSteps_cons {X : Type*} (f : X ≃ X) (fs : List (X ≃ X)) :
    fromSteps (f :: fs) = (single f).append (fromSteps fs) :=
  rfl

/-- Every certified reversible chain canonically defines an equivalence. -/
def toEquiv {X : Type*} (c : ReversibleChain X) : X ≃ X where
  toFun := c.forward.run
  invFun := c.backward.run
  left_inv := c.backward_forward
  right_inv := c.forward_backward

/-- Exact DDT duality for the whole forward chain and its inverse. -/
theorem ddt_forward_eq_backward {X A : Type*}
    [Fintype X] [DecidableEq A]
    (s : DifferenceSpace X A) (c : ReversibleChain X)
    (a b : A) :
    ddt s s c.forward.run a b = ddt s s c.backward.run b a := by
  exact ddt_equiv_symm s s c.toEquiv a b

/-- Concrete states-with-differences transport back without loss. -/
theorem restore_pair {X A : Type*}
    (s : DifferenceSpace X A) (c : ReversibleChain X)
    (p : StateDifference X A) :
    StateDifference.transport s s c.backward.run
      (StateDifference.transport s s c.forward.run p) = p := by
  exact StateDifference.transport_symm_transport s s c.toEquiv p

end ReversibleChain

end Diffan
