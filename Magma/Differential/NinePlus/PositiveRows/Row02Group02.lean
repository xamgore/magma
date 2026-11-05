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

/-- Kernel-checkable real RFC Magma trajectories: input bit 2,
    output bits 16..23. -/
theorem cell_02_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000289ba7a488943f699ab0f910b79ff4c1ce27fe01ae7bd976095b1c0f#256) ⟨k.val, by omega⟩)
      (0x5d57cba8#32, 0x11fa5eb3#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_02_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ae5f9ae3271473d5ef635f5e479eaff8cf53707c113a07c3b7d23010#256) ⟨k.val, by omega⟩)
      (0xb36edf58#32, 0x809a7adb#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_02_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bb0afee530f85ea7d6c16124e73aefefa8e075cb4e4666f6c02b2000#256) ⟨k.val, by omega⟩)
      (0xe8510db5#32, 0xc38beb1f#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_02_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001dff061d014bc41fced057c7d05f12a7b51a66f03ae6fbe959069100#256) ⟨k.val, by omega⟩)
      (0xe7e6d065#32, 0xe7f4681a#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_02_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009507e783477084e9f6defa64e9c637493789fb010b46619ed45cdf1c#256) ⟨k.val, by omega⟩)
      (0x5a7538dd#32, 0x09e85751#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_02_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007fee08254135ae4d203265e3107fa49f0e319cd50ce33062bb3741a0#256) ⟨k.val, by omega⟩)
      (0x85516bea#32, 0x64b2b68d#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_02_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006a1df74ad3bd71155f649a1fdfd4e0a93ab0cf698d46ab6538bc1000#256) ⟨k.val, by omega⟩)
      (0xbb7dede3#32, 0xadb8aaf0#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_02_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005bece27e6bbbc8f12d4e6ccba9c669068effd9b6e18ac18c63a53732#256) ⟨k.val, by omega⟩)
      (0x77585744#32, 0x50f3527f#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
