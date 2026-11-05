module

public import Difan.Algorithms.MatrixBridge
public import Magma.Differential.Bridges.DifanCarryBridge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Magma.DifanWeightedCarry — real carry matrices as Difan kernels

This module depends on both libraries; `Difan` never imports `Magma`.
Each edge counts actual nibble inputs and tracks both carry bits.
The proven 32-bit semantic bridge is reused for the eight-step count.
-/

namespace Magma.DifanWeightedCarry

open Magma
open Magma.CarryAutomaton
open Magma.DifanBridge

/-- The weight of one actual nibble transition: input/output digit
    differences are fixed, and both incoming/outgoing carry pairs
    are explicit. -/
def nibbleKernel (i : Fin 8) (keyDigit inputDiff outputDiff : Fin 16) :
    Difan.WeightKernel CarryState CarryState :=
  fun s t => sboxTransitionCount i keyDigit inputDiff outputDiff s t

/-- One local Magma transition is *exactly* the existing carry matrix. -/
theorem nibbleKernel_as_matrix (i : Fin 8) (k d b : Fin 16) :
    Difan.WeightKernel.toMatrix (nibbleKernel i k d b) =
      carryMatrix i k d b := by
  ext s t
  rfl

/-- A two-nibble convolution uses the same intermediate carry state
    as multiplication of the corresponding Magma transition matrices. -/
theorem two_nibble_convolution (i j : Fin 8)
    (ki di bi kj dj bj : Fin 16) :
    Difan.WeightKernel.toMatrix
        (Difan.WeightKernel.comp
          (nibbleKernel i ki di bi) (nibbleKernel j kj dj bj)) =
      carryMatrix i ki di bi * carryMatrix j kj dj bj := by
  calc
    Difan.WeightKernel.toMatrix
        (Difan.WeightKernel.comp
          (nibbleKernel i ki di bi) (nibbleKernel j kj dj bj)) =
      Difan.WeightKernel.toMatrix (nibbleKernel i ki di bi) *
        Difan.WeightKernel.toMatrix (nibbleKernel j kj dj bj) :=
          Difan.WeightKernel.toMatrix_comp _ _
    _ = carryMatrix i ki di bi * carryMatrix j kj dj bj := by
          rw [nibbleKernel_as_matrix, nibbleKernel_as_matrix]

/-- Reinterpret the already verified ordered product of eight Magma
    carry matrices as one natural-weighted relation on four states. -/
def eightNibbleKernel
    (key diff target : Fin 8 → Fin 16) :
    Difan.WeightKernel CarryState CarryState :=
  fun s t => carryMatrixProduct key diff target s t

/-- The generic Difan DDT of the actual Magma function is the sum
    of the four final-state weights, starting from two zero carries.
    In particular, the final carries are *not* constrained to vanish. -/
theorem ddt_g_eq_eightNibbleKernel (k d b : V 32) :
    Difan.ddt xor32 xor32 (g k) d b =
      ∑ s : CarryState,
        eightNibbleKernel (wordDigits k) (wordDigits d)
          (wordDigits (b.rotateRight 11)) (0, 0) s := by
  calc
    Difan.ddt xor32 xor32 (g k) d b =
        Magma.DifanCarryBridge.fastDDT k d b :=
          (Magma.DifanCarryBridge.fastDDT_correct k d b).symm
    _ = carryDPCount (wordDigits k) (wordDigits d)
          (wordDigits (b.rotateRight 11)) := rfl
    _ = carryMatrixCount (wordDigits k) (wordDigits d)
          (wordDigits (b.rotateRight 11)) :=
          carryDPCount_eq_carryMatrixCount _ _ _
    _ = ∑ s : CarryState,
          eightNibbleKernel (wordDigits k) (wordDigits d)
            (wordDigits (b.rotateRight 11)) (0, 0) s := rfl

/-!
# Two informative nibble-level regression checks

The first is an actual S-box-5 differential count of two inputs.
The second counts eight actual nibble-6 inputs that neutralize a
one-bit input difference when the incoming carry pair is unequal.
-/

/-- At nibble 5 with key digit 0 and input difference 3,
    exactly two input digits produce output difference 2,
    starting with both carries zero. -/
example :
    (∑ t : CarryState,
      nibbleKernel 5 0 3 2 (0, 0) t) = 2 := by
  decide

/-- At nibble 6 the input difference 1 can be canceled by unequal
    incoming carries; eight input digits yield output difference 0
    and synchronize the outgoing carries. -/
example :
    (∑ t : CarryState,
      if t.1 = t.2 then nibbleKernel 6 0 1 0 (0, 1) t else 0) = 8 := by
  decide

end Magma.DifanWeightedCarry
