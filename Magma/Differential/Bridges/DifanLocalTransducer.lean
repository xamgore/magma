module

public import Difan.Algorithms.LocalTransducer
public import Magma.Differential.Bridges.DifanWeightedCarry
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Magma.DifanLocalTransducer — actual S-box/carry steps as Difan witnesses

The local input type is Fin 16 (one nibble), the transmitted state is the
pair of carry bits, and the observation is an output XOR difference. The
kernel is definitionally the *existing* sboxTransitionCount. This is
local semantic exactness, not a new independence assumption.
-/

namespace Magma.DifanLocalTransducer

open Magma
open Magma.CarryAutomaton
open Magma.DifanWeightedCarry

/-- One requested local Magma transition, with all 4 observable parameters. -/
structure NibbleLabel where
  position : Fin 8
  keyDigit : Fin 16
  inputDiff : Fin 16
  outputDiff : Fin 16

/-- Retains the fields in the order used by sboxCarryStep. -/
def label (i : Fin 8) (k a b : Fin 16) : NibbleLabel :=
  ⟨i, k, a, b⟩

/-- Concrete semantics: local nibble x runs through the actual S-box/carry
    transformation. No probabilistic interpretation is imposed. -/
def carryLocal :
    Difan.LocalTransducer CarryState NibbleLabel (Fin 16) (Fin 16) where
  step := fun l s x =>
    sboxCarryStep l.position l.keyDigit l.inputDiff x s
  requested := fun l => l.outputDiff

/-- The induced weighted machine has the same four carry states. -/
def carryAutomaton :
    Difan.WeightedAutomaton CarryState NibbleLabel :=
  carryLocal.toAutomaton

/-- The generic Difan edge counts exactly the original Magma local fiber. -/
theorem local_weight_eq_existing (i : Fin 8) (k a b : Fin 16)
    (s t : CarryState) :
    (carryAutomaton.edge (label i k a b)) s t =
      sboxTransitionCount i k a b s t := rfl

/-- Hence the generic edge also equals the already certified nibble kernel. -/
theorem local_kernel_eq_existing (i : Fin 8) (k a b : Fin 16) :
    carryAutomaton.edge (label i k a b) = nibbleKernel i k a b := rfl

/-- Two observable steps: the generic weighted automaton performs exactly
    the same convolution as the established Magma carry matrices. -/
theorem two_nibble_as_matrices
    (i j : Fin 8) (ki ai bi kj aj bj : Fin 16) :
    Difan.WeightKernel.toMatrix
      (carryAutomaton.run [label i ki ai bi, label j kj aj bj]) =
      carryMatrix i ki ai bi * carryMatrix j kj aj bj := by
  calc
    Difan.WeightKernel.toMatrix
        (carryAutomaton.run [label i ki ai bi, label j kj aj bj]) =
      Difan.WeightKernel.toMatrix
        (Difan.WeightKernel.comp
          (carryLocal.kernel (label i ki ai bi))
          (carryLocal.kernel (label j kj aj bj))) :=
        congrArg Difan.WeightKernel.toMatrix
          (Difan.LocalTransducer.run_two carryLocal
            (label i ki ai bi) (label j kj aj bj))
    _ = carryMatrix i ki ai bi * carryMatrix j kj aj bj :=
      two_nibble_convolution i j ki ai bi kj aj bj

end Magma.DifanLocalTransducer
