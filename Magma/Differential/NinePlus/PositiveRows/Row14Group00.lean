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

/-- Kernel-checkable real RFC Magma trajectories: input bit 14,
    output bits 0..7. -/
theorem cell_14_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bea643038760358b0589126cd9a639b98f4d990aa8676cb8d496178b#256) ⟨k.val, by omega⟩)
      (0xdf9c578d#32, 0xf1d043cc#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_14_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a133c5cfd1d055da3e522eba7eea48bce7b92df96dfe12d061dcb15#256) ⟨k.val, by omega⟩)
      (0x47bb4ce9#32, 0xb5c426fa#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_14_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f3554fff3f32fbff79b60d90f75a74d3b8e8727ff47fcbef5bafe98c#256) ⟨k.val, by omega⟩)
      (0xac0db86d#32, 0x49833b90#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_14_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bf355fffe5f81252c5d2b94c8499e2828b64c645e7174bd543ed1eda#256) ⟨k.val, by omega⟩)
      (0xcc0e19fe#32, 0xd610b346#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_14_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e3232fff4e00edb535b807be332accca4ac5d7da0fbb40f1106639f3#256) ⟨k.val, by omega⟩)
      (0x9b7f74a6#32, 0x643febb1#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_14_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000042c0c0ff8ce49b3c6b5ad0897bcb09f3a927d9bec3b66883f0b7e7a0#256) ⟨k.val, by omega⟩)
      (0xaaf744af#32, 0x892e6dea#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_14_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000000f2cbfa1fe36835398a7e3728f7735baa525f49863879ccb9a900f0#256) ⟨k.val, by omega⟩)
      (0x6e4ba5c3#32, 0x731353d8#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_14_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b7493e403737d41111c8548ba7d8b8723d5dd799a360633f14caf3d2#256) ⟨k.val, by omega⟩)
      (0xac66744e#32, 0x7f58e688#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
