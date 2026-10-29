module

public import Diffan.PathCount
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Chain — exact finite chains of deterministic transformations

A chain is a list of transformations on the same state space.
For now the endomorphism assumption makes the base theorem simple;
a future heterogeneous version can use dependent vectors of types.

This module does not multiply DDT probabilities or discard base states.
-/

namespace Diffan

/-- Execute the transformations in chronological order. -/
def runChain {X : Type*} (steps : List (X → X)) (x : X) : X :=
  steps.foldl (fun state f => f state) x

@[simp]
theorem runChain_nil {X : Type*} (x : X) : runChain ([] : List (X → X)) x = x :=
  rfl

@[simp]
theorem runChain_cons {X : Type*} (f : X → X) (steps : List (X → X)) (x : X) :
    runChain (f :: steps) x = runChain steps (f x) :=
  rfl

/-- Append is exact sequential composition of two chains. -/
theorem runChain_append {X : Type*}
    (fs gs : List (X → X)) (x : X) :
    runChain (fs ++ gs) x = runChain gs (runChain fs x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change runChain (fs ++ gs) (f x) = runChain gs (runChain fs (f x))
    exact ih (f x)

/-- Carry both the *actual base state* and its current difference through
    a chain; no independence assumption or probability measure appears. -/
def propagateChain {X A : Type*}
    (s : DifferenceSpace X A) :
    List (X → X) → X → A → X × A
  | [], x, a => (x, a)
  | f :: fs, x, a =>
      propagateChain s fs (f x) (derivative s s f a x)

/-- The base state after propagation is the ordinary chain output. -/
theorem propagateChain_fst {X A : Type*}
    (s : DifferenceSpace X A) (fs : List (X → X)) (x : X) (a : A) :
    (propagateChain s fs x a).1 = runChain fs x := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs ih =>
    change (propagateChain s fs (f x) (derivative s s f a x)).1 =
      runChain fs (f x)
    exact ih (f x) (derivative s s f a x)

/-- The transported difference is exactly the derivative of the
    *composed* function, at the same original input state. -/
theorem propagateChain_snd {X A : Type*}
    (s : DifferenceSpace X A) (fs : List (X → X)) (x : X) (a : A) :
    (propagateChain s fs x a).2 =
      derivative s s (runChain fs) a x := by
  induction fs generalizing x a with
  | nil =>
      change a = s.diff x (s.shift x a)
      exact (s.diff_shift x a).symm
  | cons f fs ih =>
      change
        (propagateChain s fs (f x) (derivative s s f a x)).2 =
          derivative s s (runChain fs ∘ f) a x
      rw [derivative_comp s s s f (runChain fs) a x]
      exact ih (f x) (derivative s s f a x)

/-- Record the output difference of each step, preserving the correct
    intermediate base state and difference as the recursion proceeds. -/
def chainTrace {X A : Type*}
    (s : DifferenceSpace X A) :
    List (X → X) → X → A → List A
  | [], _, _ => []
  | f :: fs, x, a =>
      let b := derivative s s f a x
      b :: chainTrace s fs (f x) b

/-- Every physical step contributes exactly one observed difference. -/
theorem chainTrace_length {X A : Type*}
    (s : DifferenceSpace X A) (fs : List (X → X)) (x : X) (a : A) :
    (chainTrace s fs x a).length = fs.length := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs ih =>
      change (chainTrace s fs (f x) (derivative s s f a x)).length + 1 =
        fs.length + 1
      rw [ih]

/-- A finite label for the complete trajectory of differences.
    `Option` makes indexing total and makes a finite codomain even
    without manually constructing a dependent vector of list proofs. -/
def chainSignature {X A : Type*}
    (s : DifferenceSpace X A) (steps : List (X → X))
    (a : A) (x : X) : Fin steps.length → Option A :=
  fun i => (chainTrace s steps x a)[i.val]?

end Diffan
