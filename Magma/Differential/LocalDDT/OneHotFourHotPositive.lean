module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.SparsePositiveWitnesses

set_option maxRecDepth 4096

@[expose] public section

/-! ## First kernel-checked 1-hot → 4-hot positive differential -/

namespace Magma.DifanOneHotFourHotPositive

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanFiveRoundDDTReverse
open Magma.DifanSparsePositiveWitnesses

private theorem base_step_0 :
    G (0x00000000#32) (0x9e2641a9#32, 0x3754c03d#32) = (0x3754c03d#32, 0xdfffdf48#32) := by
  decide +kernel

private theorem base_step_1 :
    G (0x00002056#32) (0x3754c03d#32, 0xdfffdf48#32) = (0xdfffdf48#32, 0x52d3be05#32) := by
  decide +kernel

private theorem base_step_2 :
    G (0xfdfa7789#32) (0xdfffdf48#32, 0x52d3be05#32) = (0x52d3be05#32, 0xcf07258a#32) := by
  decide +kernel

private theorem base_step_3 :
    G (0xf0f8d960#32) (0x52d3be05#32, 0xcf07258a#32) = (0xcf07258a#32, 0x3763d53d#32) := by
  decide +kernel

private theorem base_step_4 :
    G (0x00000000#32) (0xcf07258a#32, 0x3763d53d#32) = (0x3763d53d#32, 0x987ebb6c#32) := by
  decide +kernel

private theorem base_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0x00002056#32) (0xfdfa7789#32) (0xf0f8d960#32)
          (0x00000000#32))
        (0x9e2641a9#32, 0x3754c03d#32) =
      (0x3763d53d#32, 0x987ebb6c#32) := by
  change
    G (0x00000000#32)
        (G (0xf0f8d960#32)
          (G (0xfdfa7789#32)
            (G (0x00002056#32) (G (0x00000000#32) ((0x9e2641a9#32, 0x3754c03d#32)))))) =
      (0x3763d53d#32, 0x987ebb6c#32)
  rw [base_step_0, base_step_1, base_step_2, base_step_3, base_step_4]

private theorem xor_step_0 :
    G (0x00000000#32) (0x9e264129#32, 0x3754c03d#32) = (0x3754c03d#32, 0xdfffdfc8#32) := by
  decide +kernel

private theorem xor_step_1 :
    G (0x00002056#32) (0x3754c03d#32, 0xdfffdfc8#32) = (0xdfffdfc8#32, 0x8908bdff#32) := by
  decide +kernel

private theorem xor_step_2 :
    G (0xfdfa7789#32) (0xdfffdfc8#32, 0x8908bdff#32) = (0x8908bdff#32, 0x0f072daa#32) := by
  decide +kernel

private theorem xor_step_3 :
    G (0xf0f8d960#32) (0x8908bdff#32, 0x0f072daa#32) = (0x0f072daa#32, 0x3763d53d#32) := by
  decide +kernel

private theorem xor_step_4 :
    G (0x00000000#32) (0x0f072daa#32, 0x3763d53d#32) = (0x3763d53d#32, 0x587eb34c#32) := by
  decide +kernel

private theorem xor_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0x00002056#32) (0xfdfa7789#32) (0xf0f8d960#32)
          (0x00000000#32))
        (0x9e264129#32, 0x3754c03d#32) =
      (0x3763d53d#32, 0x587eb34c#32) := by
  change
    G (0x00000000#32)
        (G (0xf0f8d960#32)
          (G (0xfdfa7789#32)
            (G (0x00002056#32) (G (0x00000000#32) ((0x9e264129#32, 0x3754c03d#32)))))) =
      (0x3763d53d#32, 0x587eb34c#32)
  rw [xor_step_0, xor_step_1, xor_step_2, xor_step_3, xor_step_4]

theorem concrete_oneHot_fourHot_delta :
    multiRoundDelta 5
        (fiveRoundKeys (0x00000000#32) (0x00002056#32) (0xfdfa7789#32) (0xf0f8d960#32)
          (0x00000000#32))
        (0x9e2641a9#32, 0x3754c03d#32) (0x00000080#32, 0#32) =
      (0#32, 0xc0000820#32) := by
  unfold multiRoundDelta
  have hxor :
    stateXor (0x9e2641a9#32, 0x3754c03d#32) (0x00000080#32, 0#32) =
      (0x9e264129#32, 0x3754c03d#32) := by
    decide +kernel
  rw [hxor, xor_five, base_five]
  decide +kernel

theorem positive_oneHot_to_fourHot :
    0 <
      xorDDT_rounds 5
        (fiveRoundKeys (0x00000000#32) (0x00002056#32) (0xfdfa7789#32) (0xf0f8d960#32)
          (0x00000000#32))
        (0x00000080#32, 0#32) (0#32, 0xc0000820#32) :=
  ddt_pos_of_concrete_base _ _ _ _ _ _ _ _ concrete_oneHot_fourHot_delta

theorem positive_fourHot_to_oneHot_reverse :
    0 <
      xorDDT_rounds 5
        (fiveRoundKeys (0x00000000#32) (0xf0f8d960#32) (0xfdfa7789#32) (0x00002056#32)
          (0x00000000#32))
        (0xc0000820#32, 0#32) (0#32, 0x00000080#32) := by
  rw [←
    outer_ddt_reverse (0x00000000#32) (0x00002056#32) (0xfdfa7789#32) (0xf0f8d960#32)
      (0x00000000#32) (0x00000080#32) (0xc0000820#32)]
  exact positive_oneHot_to_fourHot

end Magma.DifanOneHotFourHotPositive
