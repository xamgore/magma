module

import all Init.Data.Range.Basic
public import Difan.Core.Product
public import Difan.Paths.ReversibleChain
public import Magma.Differential.Bridges.DifanBridge
public import Magma.RFC8891

@[expose] public section

/-!
# Magma: reverse differential analysis of ordinary Feistel rounds

Every Magma `G k` is invertible: this is already proved by `GEquiv k`.
We specialize Difan's generic inversion theorem without proving again
how the Magma S-boxes, carry automaton, or key schedule work.

This describes sequences of ordinary `G` steps. The RFC8891 final
`GStar` uses a different output representation and requires a separate
heterogeneous boundary adapter; it is not silently inserted here.
-/

namespace Magma.DifanReverseRound

open Magma
open Magma.DifanBridge

private abbrev RoundState :=
  V 32 × V 32

/-- XOR differences componentwise on the two 32-bit Feistel halves. -/
def roundXor : Difan.DifferenceSpace RoundState RoundState :=
  Difan.DifferenceSpace.prod xor32 xor32

/-- A single Magma round is a certified reversible Difan chain. -/
def oneRound (k : V 32) : Difan.ReversibleChain RoundState :=
  Difan.ReversibleChain.single (GEquiv k)

/-- Ordinary Feistel rounds, in chronological key order. -/
def rounds (keys : List (V 32)) : Difan.ReversibleChain RoundState :=
  Difan.ReversibleChain.fromSteps (keys.map GEquiv)

/-- The input/output differences of a complete ordinary round sequence
    exchange roles when analyzing the inverse sequence. -/
theorem rounds_ddt_reverse (keys : List (V 32)) (a b : RoundState) :
    Difan.ddt roundXor roundXor (rounds keys).forward.run a b =
      Difan.ddt roundXor roundXor (rounds keys).backward.run b a := by
  exact Difan.ReversibleChain.ddt_forward_eq_backward roundXor (rounds keys) a b

/-- A genuine one-round specialization of the same equality. -/
theorem one_round_ddt_reverse (k : V 32) (a b : RoundState) :
    Difan.ddt roundXor roundXor (G k) a b =
      Difan.ddt roundXor roundXor ((GEquiv k).symm : RoundState → RoundState) b a := by
  exact Difan.ddt_equiv_symm roundXor roundXor (GEquiv k) a b

/-- Backward propagation of a concrete pair reconstructs both inputs. -/
theorem rounds_restore_pair (keys : List (V 32))
    (p : Difan.StateDifference RoundState RoundState) :
    Difan.StateDifference.transport roundXor roundXor (rounds keys).backward.run
      (Difan.StateDifference.transport roundXor roundXor
        (rounds keys).forward.run p) = p := by
  exact Difan.ReversibleChain.restore_pair roundXor (rounds keys) p

end Magma.DifanReverseRound
