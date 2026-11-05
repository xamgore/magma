module

import all Init.Data.Range.Basic
public import Diffan.Composition.KeyedMeet
public import Diffan.Composition.ReversibleMeet
public import Magma.Differential.Bridges.DiffanReverseRound
public import Magma.RFC8891

@[expose] public section

/-!
# Magma.Diffan.ScheduledMeet

Instantiate the proved `Diffan.KeyedMeet` with ONE 256-bit Magma master
key. Each list of indices is in chronological order; its 32-bit round
keys are obtained from the real deterministic `Magma.roundKey` schedule.

The midpoint retains the concrete base state and difference of the two
32-bit halves. The sequences consist of ordinary Feistel `G` rounds.
-/

namespace Magma.DiffanScheduledMeet

open Magma
open Magma.DiffanReverseRound

private abbrev RoundState :=
  V 32 × V 32

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- A sequence of *ordinary* Magma rounds chosen by indices from ONE
    master key. Repeated indices may refer to repeated round-key words. -/
def scheduledRounds (master : V 256) (indices : List (Fin 32)) :
    Diffan.ReversibleChain RoundState :=
  rounds (indices.map (roundKey master))

/-- Concrete midpoint transport through a master-key-selected prefix. -/
def leftEquiv (indices : List (Fin 32)) (master : V 256) : Point ≃ Point :=
  Diffan.ReversibleMeet.pairEquiv roundXor (scheduledRounds master indices)

/-- Concrete midpoint transport through a master-key-selected suffix. -/
def rightEquiv (indices : List (Fin 32)) (master : V 256) : Point ≃ Point :=
  Diffan.ReversibleMeet.pairEquiv roundXor (scheduledRounds master indices)

open scoped Classical in
/-- Partition witnesses by the master key shared by both halves of the execution. -/
theorem count_joined_eq_sum_by_master
    (prefixRounds suffixRounds : List (Fin 32))
    (P Q R : V 256 → Point → Prop) :
    Fintype.card
      (Diffan.KeyedMeet.Joined (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R) =
      ∑ master : V 256,
        Fintype.card
          (Diffan.Meet.EndpointFiber
            (leftEquiv prefixRounds master) (rightEquiv suffixRounds master)
            (fun initial =>
              P master initial ∧ R master (leftEquiv prefixRounds master initial))
            (Q master)) := by
  classical
  exact Diffan.KeyedMeet.card_joined_eq_sum_by_key
    (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R

/-- The same join without summing over master keys. This preserves
    actual endpoint pairs as a proof-carrying mathematical object. -/
def joinedWitnesses
    (prefixRounds suffixRounds : List (Fin 32))
    (P Q R : V 256 → Point → Prop) : Type _ :=
  Diffan.KeyedMeet.Joined (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R

end Magma.DiffanScheduledMeet
