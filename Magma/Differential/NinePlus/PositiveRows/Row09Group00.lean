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

/-- Kernel-checkable real RFC Magma trajectories: input bit 9,
    output bits 0..7. -/
theorem cell_09_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000079bf1a07138e5d26c0082ab16ad4cd9277b7648814b432806f78a26f#256) ⟨k.val, by omega⟩)
      (0x267ef685#32, 0xf15e9a73#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_09_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000034bd59ff4cd413701991744efcb17f692c072ba3ca0c2a31ccce85e6#256) ⟨k.val, by omega⟩)
      (0xed856ac3#32, 0xd23643f7#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_09_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fa1fe9ec6f67ec5dabe73bc082fa00954ca35f3688675b0e4e979e8a#256) ⟨k.val, by omega⟩)
      (0x8f304de6#32, 0x18d72fe6#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_09_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000949b4dce5c015f81824f0308fab7b4f62eecbdee656f5d8e65c32f8b#256) ⟨k.val, by omega⟩)
      (0x116b5768#32, 0x26e499f0#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_09_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bb5306ff497b603be544f680adf6c5075f82f6af217a0163cacdaf70#256) ⟨k.val, by omega⟩)
      (0x179e20f6#32, 0x83864c67#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_09_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fb353dbf9cfc6420b0964bbc05eeb66b7201f6141a6c8bbca07c569f#256) ⟨k.val, by omega⟩)
      (0xf9ea47da#32, 0x2535ab8c#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_09_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f8712cffcfd9a0d3b466f0cd4dfdf333c5949d8136549049e1da9d33#256) ⟨k.val, by omega⟩)
      (0xa319630d#32, 0x08f0eef2#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_09_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000016ca03307337781d8a5dafed2a6bb5a545be53c42c5c7ab880ad867f#256) ⟨k.val, by omega⟩)
      (0x516b0782#32, 0xbeec90de#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
