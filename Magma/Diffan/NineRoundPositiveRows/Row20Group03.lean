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

/-- Kernel-checkable real RFC Magma trajectories: input bit 20,
    output bits 24..31. -/
theorem cell_20_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002aec00000f2217109af78c1e93e7d3fcfc335747e95e11df48c60000#256) ⟨k.val, by omega⟩)
      (0x3120854f#32, 0xc1261bfd#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_20_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000da6f0000827f8ec72e76bc3a13c3341ceb957d8288513cb029800000#256) ⟨k.val, by omega⟩)
      (0x4c446121#32, 0x9735c355#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_20_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000db2be0006f4858519aea665ff4c1925157ebd8848d5e7b882b000000#256) ⟨k.val, by omega⟩)
      (0x9799d39d#32, 0x23d470da#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_20_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009f500000f4694f885e3a0f1428d64290cca3ed478e08c4c25d000000#256) ⟨k.val, by omega⟩)
      (0xfc1547c0#32, 0x0015ebcf#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_20_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000922e0080420669dd06b8758af3c158878d18a26999f11b4ede008000#256) ⟨k.val, by omega⟩)
      (0x9fc9320c#32, 0xc275d109#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_20_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000072b000005dd3b5a900602f67886655b213249a92016c0da6fc000000#256) ⟨k.val, by omega⟩)
      (0xa369e6d1#32, 0x447c1b88#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_20_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006e977800df71f67a3a1f9c6c955e155534e633ea757c5b0df80d0000#256) ⟨k.val, by omega⟩)
      (0x5a6085c4#32, 0xc0b55f3e#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_20_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e9d7f00043769dbe65c2895a43bb0e35fdf50ddbad5b9c00e0195c9e#256) ⟨k.val, by omega⟩)
      (0xf50a1de3#32, 0x20b3721c#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
