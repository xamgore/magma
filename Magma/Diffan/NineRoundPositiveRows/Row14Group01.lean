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

/-- Kernel-checkable real RFC Magma trajectories: input bit 14,
    output bits 8..15. -/
theorem cell_14_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002fb650ffb58b7fadc7159fc0b45187c655362150a8513b3b80fdbf48#256) ⟨k.val, by omega⟩)
      (0xfadb6292#32, 0x72d4e462#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_14_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000002becfffe4b5d71f7a1cebf7503e01ff1821dd5c119f1e6c87ac79fc#256) ⟨k.val, by omega⟩)
      (0x6e38d717#32, 0x0f98153e#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_14_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000022afc29258a4bf8259002cf21e6129a6655f6e65cad351d759edcdfc#256) ⟨k.val, by omega⟩)
      (0xbb070f58#32, 0x8488cae9#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_14_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000427347fc9dd26fe37e331293bd9f29aa40d2f520dc7ecd75482e1b09#256) ⟨k.val, by omega⟩)
      (0xf13a48d1#32, 0x93308ed3#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_14_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009ccf0fff9680a9348acda5940331580a5bec3ba867c49d398050d004#256) ⟨k.val, by omega⟩)
      (0xa3f9d9fa#32, 0x0550272a#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_14_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005160cfffeb0089302dbf6b0494291f33b0e527ec20d0749696442fff#256) ⟨k.val, by omega⟩)
      (0x6e33e1bd#32, 0x0e74b24c#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_14_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001b55afff331a8599eb044234fe9ea23c774d6f3b7a5529074dcd4ff6#256) ⟨k.val, by omega⟩)
      (0x71ebb190#32, 0x1dbfa33f#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_14_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005c329000783bf8f621bf90ee4c555acd28d1b02c9f315ede36b37f00#256) ⟨k.val, by omega⟩)
      (0x531f3cef#32, 0xcb1b36ac#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
