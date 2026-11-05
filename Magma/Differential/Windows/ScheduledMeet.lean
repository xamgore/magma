module

import all Init.Data.Range.Basic
public import Difan.Composition.KeyedMeet
public import Difan.Composition.ReversibleMeet
public import Magma.Differential.Bridges.DifanReverseRound
public import Magma.RFC8891

@[expose] public section

/-!
# Magma.Difan.ScheduledMeet

Instantiate the proved `Difan.KeyedMeet` with ONE 256-bit Magma master
key. Each list of indices is in chronological order; its 32-bit round
keys are obtained from the real deterministic `Magma.roundKey` schedule.

The midpoint retains the concrete base state and difference of the two
32-bit halves. The sequences consist of ordinary Feistel `G` rounds.
-/

namespace Magma.DifanScheduledMeet

open Magma
open Magma.DifanReverseRound

private abbrev RoundState :=
  V 32 × V 32

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- A sequence of *ordinary* Magma rounds chosen by indices from ONE
    master key. Repeated indices may refer to repeated round-key words. -/
def scheduledRounds (master : V 256) (indices : List (Fin 32)) :
    Difan.ReversibleChain RoundState :=
  rounds (indices.map (roundKey master))

/-- Concrete midpoint transport through a master-key-selected prefix. -/
def leftEquiv (indices : List (Fin 32)) (master : V 256) : Point ≃ Point :=
  Difan.ReversibleMeet.pairEquiv roundXor (scheduledRounds master indices)

/-- Concrete midpoint transport through a master-key-selected suffix. -/
def rightEquiv (indices : List (Fin 32)) (master : V 256) : Point ≃ Point :=
  Difan.ReversibleMeet.pairEquiv roundXor (scheduledRounds master indices)

open scoped Classical in
/-- Partition witnesses by the master key shared by both halves of the execution. -/
theorem count_joined_eq_sum_by_master
    (prefixRounds suffixRounds : List (Fin 32))
    (P Q R : V 256 → Point → Prop) :
    Fintype.card
      (Difan.KeyedMeet.Joined (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R) =
      ∑ master : V 256,
        Fintype.card
          (Difan.Meet.EndpointFiber
            (leftEquiv prefixRounds master) (rightEquiv suffixRounds master)
            (fun initial =>
              P master initial ∧ R master (leftEquiv prefixRounds master initial))
            (Q master)) := by
  classical
  exact Difan.KeyedMeet.card_joined_eq_sum_by_key
    (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R

/-- The same join without summing over master keys. This preserves
    actual endpoint pairs as a proof-carrying mathematical object. -/
def joinedWitnesses
    (prefixRounds suffixRounds : List (Fin 32))
    (P Q R : V 256 → Point → Prop) : Type _ :=
  Difan.KeyedMeet.Joined (leftEquiv prefixRounds) (rightEquiv suffixRounds) P Q R

end Magma.DifanScheduledMeet
