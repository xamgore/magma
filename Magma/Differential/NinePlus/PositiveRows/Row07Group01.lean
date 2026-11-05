module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 7,
    output bits 8..15. -/
theorem cell_07_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000781d64af7254f64fad90643f34176b42295e2bdec4141a0d8ae7bafe#256) ⟨k.val, by omega⟩)
      (0xdca5055b#32, 0x3d4773fd#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_07_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004164a0d2ec9742a21ba345d3bb3e4e7f340545fee09ea1b5b4454dc0#256) ⟨k.val, by omega⟩)
      (0x96f3d711#32, 0x04def18f#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_07_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b8b1e57b838009868a9b86971d189c260dcc388208ae352e27600602#256) ⟨k.val, by omega⟩)
      (0x562efb45#32, 0x73d87c80#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_07_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c22f4e9cebe15ca4085c9da2d90884ca22b2c5e16e1019ca778124cc#256) ⟨k.val, by omega⟩)
      (0x41c7deed#32, 0x2c10149a#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_07_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000868a308f180036153ea03f71c4bc410ea450041a7e8c3e79e710d182#256) ⟨k.val, by omega⟩)
      (0x5b22b6bd#32, 0x7c67649e#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_07_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000042c59eabe9934d8a3d6ef035e06120580aa51d3c134c4c107dcc602c#256) ⟨k.val, by omega⟩)
      (0x24fa0436#32, 0xab1aeee0#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_07_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005efd4c430435f346f9937a4978e082f895e906c1682b3f3e55d26116#256) ⟨k.val, by omega⟩)
      (0x28beb5b8#32, 0x3133191c#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_07_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000036b39730c99386ae35bda8dee33a41f556e5699b19286a47537cf01f#256) ⟨k.val, by omega⟩)
      (0xe6b85b65#32, 0x1487de12#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
