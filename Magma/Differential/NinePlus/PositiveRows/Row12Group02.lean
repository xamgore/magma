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

/-- Kernel-checkable real RFC Magma trajectories: input bit 12,
    output bits 16..23. -/
theorem cell_12_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000026c64e8005ffea6728076b0f6cfd8be550fcbb4d068985c46a72c000#256) ⟨k.val, by omega⟩)
      (0x6b67d2f2#32, 0xb6982078#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_12_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b3b1d1fe6cd5178d8928911647982278514747c3022e1f1745747ed0#256) ⟨k.val, by omega⟩)
      (0x11409bd9#32, 0x2885a9d1#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_12_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f1e8103f5e8072be8d7e1e1e99a7fa3d7fbb766a50ccb951e785f80f#256) ⟨k.val, by omega⟩)
      (0xca11ea4f#32, 0xe7d15f73#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_12_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a17f4fffc7c81e6419eb185f2a42d730b2a7aa1980cfd72bb5e87fff#256) ⟨k.val, by omega⟩)
      (0x308ed433#32, 0x58720978#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_12_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000079aaf3ff19caab3fb40d2dcd3432fd9f297d7f2aa955cc65294f03ff#256) ⟨k.val, by omega⟩)
      (0x656b44c8#32, 0x9fbdda76#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_12_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004370efffcc9b481ad5b4ab8578c12b82f6032dd3fb3bd360b2df84c0#256) ⟨k.val, by omega⟩)
      (0xeded031a#32, 0xd5442cac#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_12_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002d788f7fc289d8bc4160d5c525696b3644c739dc30b0e5bc9e6ffff6#256) ⟨k.val, by omega⟩)
      (0x47e5f6dc#32, 0x9ab8c86f#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_12_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000023ad3000500f76c27f6742c8ebae6e4ec9421b6ee7fd211c67600000#256) ⟨k.val, by omega⟩)
      (0x31459922#32, 0xa9d22394#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
