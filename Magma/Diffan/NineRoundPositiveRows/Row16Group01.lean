module
import all Init.Data.Range.Basic
public import Magma.Diffan.SixSevenRoundOuterPositive
public import Magma.Diffan.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 16,
    output bits 8..15. -/
theorem cell_16_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000962a9afcbd0523829f090af40aaa0304853cfad26ba51de5fc0ad4c0#256) ⟨k.val, by omega⟩)
      (0x98b35f82#32, 0x0b6f2c7b#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_16_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001ab47fffccfe535a7aff09edb9d40c8b4d2f00e8e26166eb44c0de60#256) ⟨k.val, by omega⟩)
      (0x083556d7#32, 0xd9e9a5f8#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_16_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000031b6e9f1ac0db1a86b09d50466428cb0a91e80eab21e6818b1aa5311#256) ⟨k.val, by omega⟩)
      (0x8b17915e#32, 0xebb6a0df#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_16_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004312fff4a55bd7e1a1bea5472bdc38202ce0536ac791f5c9276dc90a#256) ⟨k.val, by omega⟩)
      (0x3fc6cbc9#32, 0x70cba201#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_16_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e26cd14016f9b6edda1a8e208447c8198910e2458cdf43a667ed932e#256) ⟨k.val, by omega⟩)
      (0x8c485b8c#32, 0x180ec0b5#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_16_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ef27ffca82dba5d805f523c95c878808447de0b5292ea670b21ceaa#256) ⟨k.val, by omega⟩)
      (0xbaaa13db#32, 0x49b58bfc#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_16_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0c2fffd51214c7dece7dc6cef6073833cd0f5a427875be93d9a3e73#256) ⟨k.val, by omega⟩)
      (0xad71354c#32, 0x1910ad41#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_16_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000837577c09af80063b0536c8a6be0a9c48278880ceab7945b8aa1b08e#256) ⟨k.val, by omega⟩)
      (0x2b9714f0#32, 0x7bc6fa5d#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
