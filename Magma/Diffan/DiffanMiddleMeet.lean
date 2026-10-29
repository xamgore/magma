module

import all Init.Data.Range.Basic
public import Diffan.ReversibleMeet
public import Magma.Diffan.DiffanReverseRound

@[expose] public section

/-!
# Magma.DiffanMiddleMeet — exact midpoint agreement for ordinary rounds

`leftKeys` and `rightKeys` are in chronological order. The split can be
placed anywhere in a sequence of ordinary Magma Feistel rounds.

The midpoint contains both a 64-bit base state and its difference,
so the two halves describe the same concrete pair of executions.
-/

namespace Magma.DiffanMiddleMeet

open Magma
open Magma.DiffanReverseRound

private abbrev RoundState :=
  V 32 × V 32

/-- The complete middle pair from the left must equal the middle pair
    reconstructed from the right. -/
def meets (leftKeys rightKeys : List (V 32))
    (initial final : Diffan.StateDifference RoundState RoundState) : Prop :=
  Diffan.ReversibleMeet.meets roundXor
    (rounds leftKeys) (rounds rightKeys) initial final

/-- Exact meet-in-the-middle law for the real Feistel round maps.
    Forward and reverse halves refer to the SAME 64-bit state pair. -/
theorem meets_iff_forward
    (leftKeys rightKeys : List (V 32))
    (initial final : Diffan.StateDifference RoundState RoundState) :
    meets leftKeys rightKeys initial final ↔
      Diffan.StateDifference.transport roundXor roundXor
        ((rounds leftKeys).append (rounds rightKeys)).forward.run
        initial = final := by
  exact Diffan.ReversibleMeet.meets_iff_forward roundXor
    (rounds leftKeys) (rounds rightKeys) initial final

end Magma.DiffanMiddleMeet
