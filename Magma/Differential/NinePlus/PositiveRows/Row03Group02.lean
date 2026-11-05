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

/-- Kernel-checkable real RFC Magma trajectories: input bit 3,
    output bits 16..23. -/
theorem cell_03_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b6ed273523efe60109aa8d6d20564d0edff73f9c488c63475a8b0ff8#256) ⟨k.val, by omega⟩)
      (0x7de91388#32, 0xb5287ab7#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_03_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e222373910dbf9e695187bd0353e2c45d0f7c1f79ea0184884798000#256) ⟨k.val, by omega⟩)
      (0xa711b612#32, 0x3d34762e#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_03_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009762cc3d5d0619c539a65542ce486bdbcd0ea80815bff3148d03e0ec#256) ⟨k.val, by omega⟩)
      (0x8616f67d#32, 0xe48149b9#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_03_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000eec28b182a1b0ebb586c92e46dd8af1c319dc7b797c2bf7cb0b6ffbf#256) ⟨k.val, by omega⟩)
      (0xc96bf1e3#32, 0xabd996dc#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_03_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a5ad0cc584cc956a9a813671293ab5d6138e37321008bc7e55cffaf2#256) ⟨k.val, by omega⟩)
      (0xe4770519#32, 0xd32bbfc8#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_03_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000005cefb92d985ddad30ead2a030adf439e4027094332e799f58f8ff#256) ⟨k.val, by omega⟩)
      (0xf5f257c5#32, 0x308da1e0#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_03_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090f708d942d7a0c215481cc73fada5697268ff44c21a43c4d72fd0ff#256) ⟨k.val, by omega⟩)
      (0x4eb24eaf#32, 0x7b63b76b#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_03_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000064d560599dd1b0043f7985dc75600c5b277db39e1885659298ffb050#256) ⟨k.val, by omega⟩)
      (0x7959125b#32, 0xe8d35bbf#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
