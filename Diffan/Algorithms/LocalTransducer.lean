module

public import Diffan.Algorithms.WeightedAutomaton
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.LocalTransducer — local deterministic steps and exact witness fibers

Local input witnesses are counted *before* composing weighted kernels. This
supplies a concrete interpretation for each edge; a full-chain cardinality
theorem is still a separate semantic obligation.
-/

namespace Diffan

/-- A deterministic local step with a requested observable output.
    `State` is the transmitted information; `Input` is a local witness. -/
structure LocalTransducer (State Label Input Output : Type*) where
  step : Label → State → Input → Output × State
  requested : Label → Output

namespace LocalTransducer

/-- Number of concrete local inputs realizing the requested observation
    and the specified next state. This is a FINITE FIBER, not a guessed weight. -/
def kernel {S L I O : Type*} [Fintype I]
    [DecidableEq O] [DecidableEq S]
    (T : LocalTransducer S L I O) (label : L) : WeightKernel S S :=
  fun s t => ((Finset.univ : Finset I).filter
    (fun u => T.step label s u = (T.requested label, t))).card

/-- Local correctness is by construction: every weight counts precisely
    the concrete input fiber of the deterministic step. -/
theorem kernel_eq_fiber_card {S L I O : Type*} [Fintype I]
    [DecidableEq O] [DecidableEq S]
    (T : LocalTransducer S L I O) (label : L) (s t : S) :
    T.kernel label s t = ((Finset.univ : Finset I).filter
      (fun u => T.step label s u = (T.requested label, t))).card := rfl

/-- Interpret the local witness counts as a weighted automaton. -/
def toAutomaton {S L I O : Type*} [Fintype I]
    [DecidableEq O] [DecidableEq S]
    (T : LocalTransducer S L I O) : WeightedAutomaton S L where
  edge := T.kernel

/-- Two observations are combined by convolution over the *same*
    intermediate state, not by multiplying independent marginal DDTs. -/
theorem run_two {S L I O : Type*} [Fintype I]
    [Fintype S] [DecidableEq O] [DecidableEq S]
    (T : LocalTransducer S L I O) (a b : L) :
    T.toAutomaton.run [a, b] =
      WeightKernel.comp (T.kernel a) (T.kernel b) := by
  calc
    T.toAutomaton.run [a, b] =
        WeightKernel.comp (T.toAutomaton.run [a])
          (T.toAutomaton.run [b]) := by
      exact WeightedAutomaton.run_append T.toAutomaton [a] [b]
    _ = WeightKernel.comp (T.kernel a) (T.kernel b) := by
      rw [WeightedAutomaton.run_singleton, WeightedAutomaton.run_singleton]
      rfl

end LocalTransducer

end Diffan
