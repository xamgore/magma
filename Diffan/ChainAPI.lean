module

public import Diffan.ChainSimulation
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.ChainAPI — discoverable, object-oriented names for existing chains

Public wrapper, not a rewrite: old `runChain`, `propagateChain`, `chainTrace`
and their established proofs stay valid. Chain is a structure because it has
its own operations and can acquire invariants/metadata later.

For a concrete chain of Magma `g` functions, see
`Magma/DiffanChainExample.lean` in this repository.
-/

namespace Diffan

/-- A homogeneous chain of transformations. Execution is chronological. -/
structure Chain (X : Type*) where
  steps : List (X → X)

namespace Chain

/-- Empty chain / identity program. -/
def nil {X : Type*} : Chain X := ⟨[]⟩

/-- Prepend the first transformation to a chain. -/
def cons {X : Type*} (f : X → X) (c : Chain X) : Chain X :=
  ⟨f :: c.steps⟩

/-- Run the first chain, then the second. -/
def append {X : Type*} (c d : Chain X) : Chain X :=
  ⟨c.steps ++ d.steps⟩

/-- Execute a chain; delegates to the proven list-based semantics. -/
def run {X : Type*} (c : Chain X) (x : X) : X :=
  runChain c.steps x

/-- Transport the concrete base state and its current difference. -/
def propagate {X A : Type*} (c : Chain X)
    (s : DifferenceSpace X A) (x : X) (a : A) : X × A :=
  propagateChain s c.steps x a

/-- Observe the successive output differences, retaining base states internally. -/
def trace {X A : Type*} (c : Chain X)
    (s : DifferenceSpace X A) (x : X) (a : A) : List A :=
  chainTrace s c.steps x a

@[simp]
theorem run_nil {X : Type*} (x : X) : (nil : Chain X).run x = x :=
  rfl

@[simp]
theorem run_cons {X : Type*} (f : X → X) (c : Chain X) (x : X) : (cons f c).run x = c.run (f x) :=
  rfl

/-- Associativity of sequential execution, without re-proving List.foldl. -/
theorem run_append {X : Type*} (c d : Chain X) (x : X) :
    (c.append d).run x = d.run (c.run x) :=
  runChain_append c.steps d.steps x

@[simp]
theorem propagate_nil {X A : Type*} (s : DifferenceSpace X A) (x : X) (a : A) :
    (nil : Chain X).propagate s x a = (x, a) :=
  rfl

@[simp]
theorem propagate_cons {X A : Type*} (s : DifferenceSpace X A) (f : X → X) (c : Chain X) (x : X)
    (a : A) : (cons f c).propagate s x a = c.propagate s (f x) (derivative s s f a x) :=
  rfl

/-- Actual base state equals the output of the composed transformation. -/
theorem propagate_fst {X A : Type*}
    (s : DifferenceSpace X A) (c : Chain X) (x : X) (a : A) :
    (c.propagate s x a).1 = c.run x :=
  propagateChain_fst s c.steps x a

/-- Transported difference equals the exact derivative of the chain. -/
theorem propagate_snd {X A : Type*}
    (s : DifferenceSpace X A) (c : Chain X) (x : X) (a : A) :
    (c.propagate s x a).2 = derivative s s c.run a x :=
  propagateChain_snd s c.steps x a

theorem old_propagate_append {X A : Type*} (s : DifferenceSpace X A) (fs gs : List (X → X)) (x : X)
    (a : A) :
    propagateChain s (fs ++ gs) x a =
      propagateChain s gs (propagateChain s fs x a).1 (propagateChain s fs x a).2 := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change
      propagateChain s (fs ++ gs) (f x) (derivative s s f a x) =
        propagateChain s gs (propagateChain s fs (f x) (derivative s s f a x)).1
          (propagateChain s fs (f x) (derivative s s f a x)).2
    exact ih (f x) (derivative s s f a x)

/-- The second chain starts from the actual propagated state and difference. -/
theorem propagate_append {X A : Type*}
    (s : DifferenceSpace X A) (c d : Chain X) (x : X) (a : A) :
    (c.append d).propagate s x a =
      d.propagate s (c.propagate s x a).1 (c.propagate s x a).2 :=
  old_propagate_append s c.steps d.steps x a

@[simp]
theorem trace_nil {X A : Type*} (s : DifferenceSpace X A) (x : X) (a : A) :
    (nil : Chain X).trace s x a = [] :=
  rfl

@[simp]
theorem trace_cons {X A : Type*} (s : DifferenceSpace X A) (f : X → X) (c : Chain X) (x : X)
    (a : A) :
    (cons f c).trace s x a = derivative s s f a x :: c.trace s (f x) (derivative s s f a x) :=
  rfl

theorem trace_length {X A : Type*} (s : DifferenceSpace X A) (c : Chain X) (x : X) (a : A) :
    (c.trace s x a).length = c.steps.length :=
  chainTrace_length s c.steps x a

theorem old_trace_append {X A : Type*} (s : DifferenceSpace X A) (fs gs : List (X → X)) (x : X)
    (a : A) :
    chainTrace s (fs ++ gs) x a =
      chainTrace s fs x a ++
        chainTrace s gs (propagateChain s fs x a).1 (propagateChain s fs x a).2 := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change
      derivative s s f a x :: chainTrace s (fs ++ gs) (f x) (derivative s s f a x) =
        derivative s s f a x ::
          (chainTrace s fs (f x) (derivative s s f a x) ++
            chainTrace s gs (propagateChain s fs (f x) (derivative s s f a x)).1
              (propagateChain s fs (f x) (derivative s s f a x)).2)
    exact congrArg (List.cons (derivative s s f a x)) (ih (f x) (derivative s s f a x))

/-- The second trace must begin at the propagated state/difference. -/
theorem trace_append {X A : Type*}
    (s : DifferenceSpace X A) (c d : Chain X) (x : X) (a : A) :
    (c.append d).trace s x a =
      c.trace s x a ++
      d.trace s (c.propagate s x a).1 (c.propagate s x a).2 :=
  old_trace_append s c.steps d.steps x a

end Chain

end Diffan
