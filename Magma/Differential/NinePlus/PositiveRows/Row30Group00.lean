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

/-- Kernel-checkable real RFC Magma trajectories: input bit 30,
    output bits 0..7. -/
theorem cell_30_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006000b000b78fd2e2021118fd6b88e1b7e8066eb77e366bdb40bf3cbf#256) ⟨k.val, by omega⟩)
      (0xb92d559a#32, 0xa52e820c#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_30_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000be0100005ed06578572dcc95822085c3ba5cade0d6c103515db1d26a#256) ⟨k.val, by omega⟩)
      (0x9d507b02#32, 0x56270490#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_30_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005800008039de328e7497ec34be6240354b8334a215e759d095522e33#256) ⟨k.val, by omega⟩)
      (0x62115e71#32, 0xed00d83c#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_30_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002042effbe12a495c00b230d5916d058cb0d5ec6cc517992b08728901#256) ⟨k.val, by omega⟩)
      (0xad4e598a#32, 0x2663bce1#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_30_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009800a000a779edf074eb043b754abe84df38dfb779b793899f89daa8#256) ⟨k.val, by omega⟩)
      (0xd3482ed4#32, 0x8ce5a994#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_30_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d000000032a454f891ddc19df45bfcf4f3a40e9ddf7ef40e129acfe0#256) ⟨k.val, by omega⟩)
      (0x688ee81f#32, 0xbe789e72#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_30_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002000c000d0f3059e814b2b9695b2bae0591b901784965842f206ff30#256) ⟨k.val, by omega⟩)
      (0x9567561b#32, 0x05aa379c#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_30_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005800000090c3669ce0e504c0a83e9eae09780adcea8a9fe039e67160#256) ⟨k.val, by omega⟩)
      (0x13dd30e1#32, 0x1f99f12f#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
