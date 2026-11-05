module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.SparsePositiveWitnesses

set_option maxRecDepth 4096

@[expose] public section

/-! A concrete five-round general-diagonal counterexample to naive
    extensions of the OUTER weight-sum bound to both active halves.
    One bit is active in each half at the input and at the output. -/

namespace Magma.DifanAdjacentPositiveExample

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanSparsePositiveWitnesses

private theorem base_step_0 :
    G (0x495958a8#32) (0x0706b966#32, 0x56ae5f4f#32) = (0x56ae5f4f#32, 0xede97424#32) := by
  decide +kernel

private theorem base_step_1 :
    G (0xc7c68ae4#32) (0x56ae5f4f#32, 0xede97424#32) = (0xede97424#32, 0x332d2c03#32) := by
  decide +kernel

private theorem base_step_2 :
    G (0xfa7ff536#32) (0xede97424#32, 0x332d2c03#32) = (0x332d2c03#32, 0xccf0b370#32) := by
  decide +kernel

private theorem base_step_3 :
    G (0xf3b7b60c#32) (0x332d2c03#32, 0xccf0b370#32) = (0xccf0b370#32, 0x34a328c7#32) := by
  decide +kernel

private theorem base_step_4 :
    G (0x7f0cd739#32) (0xccf0b370#32, 0x34a328c7#32) = (0x34a328c7#32, 0x72abd058#32) := by
  decide +kernel

private theorem base_five :
    iterateG 5
        (fiveRoundKeys (0x495958a8#32) (0xc7c68ae4#32) (0xfa7ff536#32) (0xf3b7b60c#32)
          (0x7f0cd739#32))
        (0x0706b966#32, 0x56ae5f4f#32) =
      (0x34a328c7#32, 0x72abd058#32) := by
  change
    G (0x7f0cd739#32)
        (G (0xf3b7b60c#32)
          (G (0xfa7ff536#32)
            (G (0xc7c68ae4#32) (G (0x495958a8#32) ((0x0706b966#32, 0x56ae5f4f#32)))))) =
      (0x34a328c7#32, 0x72abd058#32)
  rw [base_step_0, base_step_1, base_step_2, base_step_3, base_step_4]

private theorem altered_step_0 :
    G (0x495958a8#32) (0x0706b967#32, 0x56a65f4f#32) = (0x56a65f4f#32, 0x65e976df#32) := by
  decide +kernel

private theorem altered_step_1 :
    G (0xc7c68ae4#32) (0x56a65f4f#32, 0x65e976df#32) = (0x65e976df#32, 0xe8bbc81f#32) := by
  decide +kernel

private theorem altered_step_2 :
    G (0xfa7ff536#32) (0x65e976df#32, 0xe8bbc81f#32) = (0xe8bbc81f#32, 0x17245b74#32) := by
  decide +kernel

private theorem altered_step_3 :
    G (0xf3b7b60c#32) (0xe8bbc81f#32, 0x17245b74#32) = (0x17245b74#32, 0x34a328c6#32) := by
  decide +kernel

private theorem altered_step_4 :
    G (0x7f0cd739#32) (0x17245b74#32, 0x34a328c6#32) = (0x34a328c6#32, 0x72a3d058#32) := by
  decide +kernel

private theorem altered_five :
    iterateG 5
        (fiveRoundKeys (0x495958a8#32) (0xc7c68ae4#32) (0xfa7ff536#32) (0xf3b7b60c#32)
          (0x7f0cd739#32))
        (0x0706b967#32, 0x56a65f4f#32) =
      (0x34a328c6#32, 0x72a3d058#32) := by
  change
    G (0x7f0cd739#32)
        (G (0xf3b7b60c#32)
          (G (0xfa7ff536#32)
            (G (0xc7c68ae4#32) (G (0x495958a8#32) ((0x0706b967#32, 0x56a65f4f#32)))))) =
      (0x34a328c6#32, 0x72a3d058#32)
  rw [altered_step_0, altered_step_1, altered_step_2, altered_step_3, altered_step_4]

theorem general_diagonal_trajectory :
    multiRoundDelta 5
        (fiveRoundKeys (0x495958a8#32) (0xc7c68ae4#32) (0xfa7ff536#32) (0xf3b7b60c#32)
          (0x7f0cd739#32))
        (0x0706b966#32, 0x56ae5f4f#32) (0x00000001#32, 0x00080000#32) =
      (0x00000001#32, 0x00080000#32) := by
  unfold multiRoundDelta
  have hx :
    stateXor (0x0706b966#32, 0x56ae5f4f#32) (0x00000001#32, 0x00080000#32) =
      (0x0706b967#32, 0x56a65f4f#32) := by
    decide +kernel
  rw [hx, altered_five, base_five]
  decide +kernel

theorem general_diagonal_ddt_positive :
    0 <
      xorDDT_rounds 5
        (fiveRoundKeys (0x495958a8#32) (0xc7c68ae4#32) (0xfa7ff536#32) (0xf3b7b60c#32)
          (0x7f0cd739#32))
        (0x00000001#32, 0x00080000#32) (0x00000001#32, 0x00080000#32) :=
  ddt_pos_of_concrete_base _ _ _ _ _ _ _ _ general_diagonal_trajectory

end Magma.DifanAdjacentPositiveExample
