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

/-- Kernel-checkable real RFC Magma trajectories: input bit 28,
    output bits 8..15. -/
theorem cell_28_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7b00000b364ab6ddddedb5c4d5e00eed9a8868b136ba5e5d53b6b00#256) ⟨k.val, by omega⟩)
      (0x021d16ab#32, 0x72ead13f#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_28_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ee030000f7fb049f15655ad57cbec503be1c64624774aa5558e65dc0#256) ⟨k.val, by omega⟩)
      (0xddbb40ab#32, 0xc2156470#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_28_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000048020000ef9bd7549ce5c62f2958184edc120452a071f51044c2bd08#256) ⟨k.val, by omega⟩)
      (0x713cc84c#32, 0x8fda0072#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_28_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006f880000792fc359088a1073f42b0515fcdda772a7ce8fa2dd913f00#256) ⟨k.val, by omega⟩)
      (0x6e297498#32, 0x21f04b65#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_28_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0800000bb6786627a72cb455fdf07fc27c7337cabe324480f64b000#256) ⟨k.val, by omega⟩)
      (0x663dca7a#32, 0x7ada6d47#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_28_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000028000000c3ac7c8b0603588585f1d20660be19e6fe4f45bf3fbdb000#256) ⟨k.val, by omega⟩)
      (0x2e7a11cf#32, 0xbb6e4247#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_28_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050000000578aed150978c4a7d1ff89d917e701ada5e400b88fb19000#256) ⟨k.val, by omega⟩)
      (0xe609e87a#32, 0x6a943120#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_28_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f65fc0007d3a0b121a52fc20de84929dcec7280fe8429298e7185000#256) ⟨k.val, by omega⟩)
      (0x6ba4d660#32, 0x99c8444d#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
