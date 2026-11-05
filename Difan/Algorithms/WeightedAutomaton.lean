module

public import Difan.Algorithms.WeightedKernel
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.WeightedAutomaton — algebra of finite weighted state machines

The run operator composes local kernels in chronological order. This is an
algebraic theorem; no claim about a concrete program's witness counts is
made until a separate semantic certificate is supplied.
-/

namespace Difan

/-- Exact left and right identity laws for natural-number kernels. -/
@[simp] theorem WeightKernel.id_comp {S T : Type*}
    [Fintype S] [DecidableEq S] (w : WeightKernel S T) :
    WeightKernel.comp (WeightKernel.id S) w = w := by
  funext s t
  classical
  simp [WeightKernel.comp, WeightKernel.id]

@[simp]
theorem WeightKernel.comp_id {S T : Type*} [Fintype T] [DecidableEq T] (w : WeightKernel S T) :
    WeightKernel.comp w (WeightKernel.id T) = w := by
  funext s t
  classical simp [WeightKernel.comp, WeightKernel.id]

/-- An automaton described by a finite family of weighted relations. -/
structure WeightedAutomaton (State Label : Type*) where
  edge : Label → WeightKernel State State

namespace WeightedAutomaton

/-- A list of observations, interpreted as consecutive matrix products. -/
def run {State Label : Type*} [Fintype State] [DecidableEq State]
    (M : WeightedAutomaton State Label) :
    List Label → WeightKernel State State
  | [] => WeightKernel.id State
  | a :: rest => WeightKernel.comp (M.edge a) (M.run rest)

@[simp]
theorem run_nil {State Label : Type*} [Fintype State] [DecidableEq State]
    (M : WeightedAutomaton State Label) : M.run [] = WeightKernel.id State :=
  rfl

@[simp]
theorem run_cons {State Label : Type*} [Fintype State] [DecidableEq State]
    (M : WeightedAutomaton State Label) (a : Label) (rest : List Label) :
    M.run (a :: rest) = WeightKernel.comp (M.edge a) (M.run rest) :=
  rfl

@[simp]
theorem run_singleton {State Label : Type*} [Fintype State] [DecidableEq State]
    (M : WeightedAutomaton State Label) (a : Label) : M.run [a] = M.edge a := by
  change WeightKernel.comp (M.edge a) (WeightKernel.id State) = M.edge a
  exact WeightKernel.comp_id (M.edge a)

/-- Appending observation sequences corresponds to kernel composition. -/
theorem run_append {State Label : Type*}
    [Fintype State] [DecidableEq State]
    (M : WeightedAutomaton State Label) (xs ys : List Label) :
    M.run (xs ++ ys) = WeightKernel.comp (M.run xs) (M.run ys) := by
  induction xs with
  | nil =>
      change M.run ys = WeightKernel.comp (WeightKernel.id State) (M.run ys)
      exact (WeightKernel.id_comp (M.run ys)).symm
  | cons a rest ih =>
      calc
        M.run ((a :: rest) ++ ys) =
            WeightKernel.comp (M.edge a) (M.run (rest ++ ys)) := rfl
        _ = WeightKernel.comp (M.edge a)
              (WeightKernel.comp (M.run rest) (M.run ys)) := by rw [ih]
        _ = WeightKernel.comp (M.run (a :: rest)) (M.run ys) :=
              (WeightKernel.comp_assoc (M.edge a) (M.run rest) (M.run ys)).symm

end WeightedAutomaton

end Difan
