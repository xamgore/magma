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

/-- Kernel-checkable real RFC Magma trajectories: input bit 23,
    output bits 16..23. -/
theorem cell_23_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e6bffffff8684b0daf5c8c12d61dc631ab9e05f1e3b0de724d72f7ef#256) ⟨k.val, by omega⟩)
      (0xa49ab792#32, 0x7cc1faf9#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_23_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005d800000a4021d674168b14a5ee899d39080f6a065c6a81efeca0000#256) ⟨k.val, by omega⟩)
      (0xb91f940d#32, 0x28c08281#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_23_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f23000003378071d67195a1bf076fd18dec1a30773f25c157f6d3000#256) ⟨k.val, by omega⟩)
      (0x0d20b880#32, 0x0f5e3836#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_23_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f97000006c7643bd1f6489438ff3ec4ff381c6547010f08d5a610000#256) ⟨k.val, by omega⟩)
      (0x5f307cab#32, 0xd8b72ca4#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_23_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000094c7ffff32e7a525e543a62dea6d43fb854565da6ffab7af0c678ff8#256) ⟨k.val, by omega⟩)
      (0x2cd69f3f#32, 0x1b4bb35f#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_23_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000fb0000049d8268e9af7c5fbffaca6d0a9a9fb7edfb5087ad1580000#256) ⟨k.val, by omega⟩)
      (0xa5e0bcc6#32, 0x5564a878#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_23_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ab700000087bb3ad14fcea2248a7894c1a49aea5187f8004440000d0#256) ⟨k.val, by omega⟩)
      (0xa539e014#32, 0xf39dc402#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_23_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c4780000d76aa1dce81c035aefa6c2c46f7d8e23a741da7e7eb80000#256) ⟨k.val, by omega⟩)
      (0x66096dfc#32, 0x05d5f344#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
