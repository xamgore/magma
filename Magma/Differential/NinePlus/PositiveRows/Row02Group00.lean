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
    output bits 0..7. -/
theorem cell_02_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a8f0ef0da0b4908fc4f05570c0c25cab8423e8842bca9e7086bf2c1b#256) ⟨k.val, by omega⟩)
      (0x3c672e66#32, 0x32ac77eb#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_02_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000145fa3b4aa755a15e99b0293065f8829bf775eab2fee15897067ec96#256) ⟨k.val, by omega⟩)
      (0x83afa9c4#32, 0xe64629f8#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_02_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c6ff1e13dab5b17eeef73437d95b8b9e0cd654e64c20808be1231efc#256) ⟨k.val, by omega⟩)
      (0x6316bec6#32, 0x23372876#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_02_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f13ca39f8917434697dc22237a42de71d49328ff79ee567f9b7445eb#256) ⟨k.val, by omega⟩)
      (0xe4b12962#32, 0xab1b98a8#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_02_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ccffb6c6223773f88fd03c4e07702f7a00de6c7a1ad78dfbe339cd77#256) ⟨k.val, by omega⟩)
      (0x7f2dde66#32, 0x2a69a0c3#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_02_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bdce20fa67c7a706a592c19e3708d97bb226ff3c2e3c335bdc8a80a0#256) ⟨k.val, by omega⟩)
      (0xa67627c1#32, 0x000813fe#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_02_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a6406ea70f37f9a3526b8133b75cb127a1c01a687df106746119ba30#256) ⟨k.val, by omega⟩)
      (0x73bf0143#32, 0x4e3d9f83#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_02_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d346e045aa6eed9c41c1ef86a2dde8958bede40b3700a305971a5fb2#256) ⟨k.val, by omega⟩)
      (0x5a57bb4b#32, 0xc190f7d1#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
