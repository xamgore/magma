module

import all Init.Data.Range.Basic
public import Diffan.Product
public import Diffan.ReversibleChain
public import Magma.Diffan.DiffanBridge
public import Magma.RFC8891

@[expose] public section

/-!
# Magma: reverse differential analysis of ordinary Feistel rounds

Every Magma `G k` is invertible: this is already proved by `GEquiv k`.
We specialize Diffan's generic inversion theorem without proving again
how the Magma S-boxes, carry automaton, or key schedule work.

This describes sequences of ordinary `G` steps. The RFC8891 final
`GStar` uses a different output representation and requires a separate
heterogeneous boundary adapter; it is not silently inserted here.
-/

namespace Magma.DiffanReverseRound

open Magma
open Magma.DiffanBridge

private abbrev RoundState :=
  V 32 × V 32

/-- XOR differences componentwise on the two 32-bit Feistel halves. -/
def roundXor : Diffan.DifferenceSpace RoundState RoundState :=
  Diffan.DifferenceSpace.prod xor32 xor32

/-- A single Magma round is a certified reversible Diffan chain. -/
def oneRound (k : V 32) : Diffan.ReversibleChain RoundState :=
  Diffan.ReversibleChain.single (GEquiv k)

/-- Ordinary Feistel rounds, in chronological key order. -/
def rounds (keys : List (V 32)) : Diffan.ReversibleChain RoundState :=
  Diffan.ReversibleChain.fromSteps (keys.map GEquiv)

/-- The input/output differences of a complete ordinary round sequence
    exchange roles when analyzing the inverse sequence. -/
theorem rounds_ddt_reverse (keys : List (V 32)) (a b : RoundState) :
    Diffan.ddt roundXor roundXor (rounds keys).forward.run a b =
      Diffan.ddt roundXor roundXor (rounds keys).backward.run b a := by
  exact Diffan.ReversibleChain.ddt_forward_eq_backward roundXor (rounds keys) a b

/-- A genuine one-round specialization of the same equality. -/
theorem one_round_ddt_reverse (k : V 32) (a b : RoundState) :
    Diffan.ddt roundXor roundXor (G k) a b =
      Diffan.ddt roundXor roundXor ((GEquiv k).symm : RoundState → RoundState) b a := by
  exact Diffan.ddt_equiv_symm roundXor roundXor (GEquiv k) a b

/-- Backward propagation of a concrete pair reconstructs both inputs. -/
theorem rounds_restore_pair (keys : List (V 32))
    (p : Diffan.StateDifference RoundState RoundState) :
    Diffan.StateDifference.transport roundXor roundXor (rounds keys).backward.run
      (Diffan.StateDifference.transport roundXor roundXor
        (rounds keys).forward.run p) = p := by
  exact Diffan.ReversibleChain.restore_pair roundXor (rounds keys) p

end Magma.DiffanReverseRound
