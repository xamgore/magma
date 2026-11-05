module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 22,
    output bits 16..23. -/
theorem cell_22_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000af100000688302790b95a7d2f7337d42333c70ed39e3487644468000#256) ⟨k.val, by omega⟩)
      (0x3ebae619#32, 0x695509b3#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_22_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dec1ffff65c461ceed741bbb189723e433f728fcab5c4ac64302d800#256) ⟨k.val, by omega⟩)
      (0x8474a2d4#32, 0xaff3a2e8#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_22_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cfd71cd41dc54ca0f4faef4ca93515ebce8f74e42e65636531939c00#256) ⟨k.val, by omega⟩)
      (0x86f9cb7a#32, 0x6dfd4bad#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_22_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000086d0807f4d96601f7d1b2f5b20329c0b3c1a5adc13972ab45d9ab7f8#256) ⟨k.val, by omega⟩)
      (0x59974c43#32, 0x8539503b#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_22_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a3e00000f82195de9b2f1b4c8e2eaef0962cf8fbba02e89d0e5b0000#256) ⟨k.val, by omega⟩)
      (0xe6f4e844#32, 0x83b8eaaf#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_22_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000039600000da5c802275547a815493179f099b3665f623429873d80000#256) ⟨k.val, by omega⟩)
      (0x33674d86#32, 0xa76b1d9d#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_22_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000011be0000db1f71c17b271110939e2907bb860c2c249806780b200000#256) ⟨k.val, by omega⟩)
      (0x26cbfbdc#32, 0x69273238#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_22_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003e3af5ed056562687a62aa728405f0f6b24af16bed1ab25d7d391f46#256) ⟨k.val, by omega⟩)
      (0xfd9e07eb#32, 0x98d515a5#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
