module

public import Diffan.Core.StateDifference
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.Chain — exact finite chains of deterministic transformations

A `Chain X` is a sequence of transformations `X → X`. Its members run
in chronological order: `Chain.cons f (Chain.cons g Chain.nil)` first runs
`f`, then `g`. More general heterogeneous chains are a separate future topic.

This module distinguishes three kinds of information:

* `Chain.run` computes an **actual state** after all transformations.
* `Chain.propagateState` retains the actual base state and its **current difference**.
* `Chain.trace` records every intermediate output difference. Its internal
  recursion passes the actual base state to the next step, rather than
  treating independent DDT entries as a joint trajectory.

A chain never assumes independence or multiplication of DDT probabilities.
The only data field is the list of steps; recursion over lists is an
implementation detail, not a second public API.
-/

namespace Diffan

/-- A homogeneous chain: all transformations share their state space.
    The order of `steps` is the order in which transformations execute. -/
structure Chain (X : Type*) where
  steps : List (X → X)

namespace Chain

/-! ## Internal recursive semantics on the list of transformations

The helper functions and their proofs are file-private. They exist so public
`Chain.*` laws can reuse simple structural inductions on `List`, rather than
reproving them each time for the wrapper `Chain`.
-/

/-- Run each step on the *actual* state produced by the preceding step. -/
private def runSteps {X : Type*} (steps : List (X → X)) (x : X) : X :=
  steps.foldl (fun state f => f state) x

private theorem runSteps_append {X : Type*} (fs gs : List (X → X)) (x : X) :
    runSteps (fs ++ gs) x = runSteps gs (runSteps fs x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    change runSteps (fs ++ gs) (f x) = runSteps gs (runSteps fs (f x))
    exact ih (f x)

/-- Transport the actual base point and current difference together.
    The derivative of each step is evaluated at the correct current state. -/
private def propagateSteps {X A : Type*}
    (s : DifferenceSpace X A) :
    List (X → X) → X → A → X × A
  | [], x, a => (x, a)
  | f :: fs, x, a =>
      propagateSteps s fs (f x) (derivative s s f a x)

private theorem propagateSteps_fst {X A : Type*} (s : DifferenceSpace X A) (fs : List (X → X))
    (x : X) (a : A) : (propagateSteps s fs x a).1 = runSteps fs x := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change (propagateSteps s fs (f x) (derivative s s f a x)).1 = runSteps fs (f x)
    exact ih (f x) (derivative s s f a x)

private theorem propagateSteps_snd {X A : Type*} (s : DifferenceSpace X A) (fs : List (X → X))
    (x : X) (a : A) : (propagateSteps s fs x a).2 = derivative s s (runSteps fs) a x := by
  induction fs generalizing x a with
  | nil =>
    change a = s.diff x (s.shift x a)
    exact (s.diff_shift x a).symm
  | cons f fs
    ih =>
    change
      (propagateSteps s fs (f x) (derivative s s f a x)).2 = derivative s s (runSteps fs ∘ f) a x
    rw [derivative_comp s s s f (runSteps fs) a x]
    exact ih (f x) (derivative s s f a x)

private theorem propagateSteps_append {X A : Type*} (s : DifferenceSpace X A) (fs gs : List (X → X))
    (x : X) (a : A) :
    propagateSteps s (fs ++ gs) x a =
      propagateSteps s gs (propagateSteps s fs x a).1 (propagateSteps s fs x a).2 := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change
      propagateSteps s (fs ++ gs) (f x) (derivative s s f a x) =
        propagateSteps s gs (propagateSteps s fs (f x) (derivative s s f a x)).1
          (propagateSteps s fs (f x) (derivative s s f a x)).2
    exact ih (f x) (derivative s s f a x)

/-- Record the output difference of *each* step, advancing the actual
    base state and difference through the recursion. -/
private def traceSteps {X A : Type*}
    (s : DifferenceSpace X A) :
    List (X → X) → X → A → List A
  | [], _, _ => []
  | f :: fs, x, a =>
      let b := derivative s s f a x
      b :: traceSteps s fs (f x) b

private theorem traceSteps_length {X A : Type*} (s : DifferenceSpace X A) (fs : List (X → X))
    (x : X) (a : A) : (traceSteps s fs x a).length = fs.length := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change (traceSteps s fs (f x) (derivative s s f a x)).length + 1 = fs.length + 1
    rw [ih]

private theorem traceSteps_append {X A : Type*} (s : DifferenceSpace X A) (fs gs : List (X → X))
    (x : X) (a : A) :
    traceSteps s (fs ++ gs) x a =
      traceSteps s fs x a ++
        traceSteps s gs (propagateSteps s fs x a).1 (propagateSteps s fs x a).2 := by
  induction fs generalizing x a with
  | nil => rfl
  | cons f fs
    ih =>
    change
      derivative s s f a x :: traceSteps s (fs ++ gs) (f x) (derivative s s f a x) =
        derivative s s f a x ::
          (traceSteps s fs (f x) (derivative s s f a x) ++
            traceSteps s gs (propagateSteps s fs (f x) (derivative s s f a x)).1
              (propagateSteps s fs (f x) (derivative s s f a x)).2)
    exact congrArg (List.cons (derivative s s f a x)) (ih (f x) (derivative s s f a x))

/-! ## Construction and execution -/

/-- The empty chain is the identity transformation. -/
def nil {X : Type*} : Chain X := ⟨[]⟩

/-- Prepend the first transformation to a chain. -/
def cons {X : Type*} (f : X → X) (c : Chain X) : Chain X :=
  ⟨f :: c.steps⟩

/-- Execute `c` first, then execute `d`. -/
def append {X : Type*} (c d : Chain X) : Chain X :=
  ⟨c.steps ++ d.steps⟩

/-- Execute the transformations in chronological order. -/
def run {X : Type*} (c : Chain X) (x : X) : X :=
  runSteps c.steps x

@[simp]
theorem run_nil {X : Type*} (x : X) : (nil : Chain X).run x = x :=
  rfl

@[simp]
theorem run_cons {X : Type*} (f : X → X) (c : Chain X) (x : X) : (cons f c).run x = c.run (f x) :=
  rfl

/-- Sequential execution respects append; there is no reversed order. -/
theorem run_append {X : Type*} (c d : Chain X) (x : X) :
    (c.append d).run x = d.run (c.run x) :=
  runSteps_append c.steps d.steps x

/-! ## Difference propagation and trajectory observations -/

/-- A nonlinear step needs the actual base state as well as its difference.
    Keeping both coordinates follows the same concrete pair through the chain. -/
def propagateState {X A : Type*}
    (c : Chain X) (s : DifferenceSpace X A)
    (p : StateDifference X A) : StateDifference X A :=
  let result := propagateSteps s c.steps p.base p.delta
  ⟨result.1, result.2⟩

@[simp]
theorem propagateState_nil {X A : Type*} (s : DifferenceSpace X A) (p : StateDifference X A) :
    (nil : Chain X).propagateState s p = p :=
  rfl

@[simp]
theorem propagateState_cons {X A : Type*} (s : DifferenceSpace X A) (f : X → X) (c : Chain X)
    (p : StateDifference X A) :
    (cons f c).propagateState s p = c.propagateState s (p.transport s s f) :=
  rfl

/-- The initial state fixes the concrete output independently of which
    difference is being studied alongside it. -/
theorem propagateState_base {X A : Type*}
    (c : Chain X) (s : DifferenceSpace X A) (p : StateDifference X A) :
    (c.propagateState s p).base = c.run p.base :=
  propagateSteps_fst s c.steps p.base p.delta

/-- Retaining the base state connects the final observation to the
    derivative at the original input, rather than a marginal support path. -/
theorem propagateState_delta {X A : Type*}
    (c : Chain X) (s : DifferenceSpace X A) (p : StateDifference X A) :
    (c.propagateState s p).delta = derivative s s c.run p.delta p.base :=
  propagateSteps_snd s c.steps p.base p.delta

/-- The second chain starts with both coordinates left by the first. -/
theorem propagateState_comp {X A : Type*}
    (c d : Chain X) (s : DifferenceSpace X A) (p : StateDifference X A) :
    (c.append d).propagateState s p =
      d.propagateState s (c.propagateState s p) := by
  rcases p with ⟨x, a⟩
  simp only [propagateState, append, propagateSteps_append]

/-- Entries are recorded after steps, so the initial difference has no entry.
    An empty chain has an empty trace but still propagates its input difference. -/
def trace {X A : Type*} (c : Chain X)
    (s : DifferenceSpace X A) (x : X) (a : A) : List A :=
  traceSteps s c.steps x a

@[simp]
theorem trace_nil {X A : Type*} (s : DifferenceSpace X A) (x : X) (a : A) :
    (nil : Chain X).trace s x a = [] :=
  rfl

@[simp]
theorem trace_cons {X A : Type*} (s : DifferenceSpace X A) (f : X → X) (c : Chain X) (x : X)
    (a : A) :
    (cons f c).trace s x a = derivative s s f a x :: c.trace s (f x) (derivative s s f a x) :=
  rfl

/-- Every physical step contributes exactly one output difference. -/
theorem trace_length {X A : Type*}
    (s : DifferenceSpace X A) (c : Chain X) (x : X) (a : A) :
    (c.trace s x a).length = c.steps.length :=
  traceSteps_length s c.steps x a

/-- The second trace begins at the actual propagated state/difference.
    It is NOT a concatenation of independently sampled DDT paths. -/
theorem trace_append {X A : Type*}
    (s : DifferenceSpace X A) (c d : Chain X) (x : X) (a : A) :
    (c.append d).trace s x a =
      c.trace s x a ++
      d.trace s (c.propagateState s ⟨x, a⟩).base (c.propagateState s ⟨x, a⟩).delta :=
  traceSteps_append s c.steps d.steps x a

/-- Finite label of the complete difference trajectory. Using `Option`
    makes out-of-range access total; the label domain is finite whenever
    the difference type is finite. This is useful for exact DDT partitions. -/
def signature {X A : Type*}
    (c : Chain X) (s : DifferenceSpace X A) (a : A) (x : X) :
    Fin c.steps.length → Option A :=
  fun i => (c.trace s x a)[i.val]?

end Chain

end Diffan
