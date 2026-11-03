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

/-- Kernel-checkable real RFC Magma trajectories: input bit 18,
    output bits 16..23. -/
theorem cell_18_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002a6600005246a1b5cd3d46d9edbbf9c24071013d018bd1fcdaca8000#256) ⟨k.val, by omega⟩)
      (0x25d527dd#32, 0xc6a49d25#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_18_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000056647fff72c8db35fe7b7d23cbfd82398df38dcc514174addc5b3cd0#256) ⟨k.val, by omega⟩)
      (0x1ff43392#32, 0xbf151917#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_18_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002021ffffa8bccd90ff564bdbe6203b604dea192a0dab9d392a81ff8f#256) ⟨k.val, by omega⟩)
      (0xfda4f65b#32, 0x8af45504#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_18_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000467b0886a553d496216284c355141dc655c93ba2053a64de3ad9fd85#256) ⟨k.val, by omega⟩)
      (0x4e71a8c8#32, 0x35c8ef9d#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_18_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005ca2ffff6f8d76743b53f28d4545268d78e27e3da67392f50ffcfc30#256) ⟨k.val, by omega⟩)
      (0x166a52ed#32, 0x68d65e48#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_18_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000daa0000cd7b6d0eb58837dfb5157914c3cce1b5377cbd9d244dfe09#256) ⟨k.val, by omega⟩)
      (0x6b7a8e50#32, 0x090c2229#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_18_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003beb7e539082817a31b879f3eb2c0092161f5a58152d91d6b5c003c0#256) ⟨k.val, by omega⟩)
      (0x8c41f8b2#32, 0x519adeb8#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_18_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a181ffff9d1e0fe3eff417b50c973de9fe4616e7abff99491e98a8c0#256) ⟨k.val, by omega⟩)
      (0x4f78f45f#32, 0x89c4d041#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
