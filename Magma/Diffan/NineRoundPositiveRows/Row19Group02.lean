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

/-- Kernel-checkable real RFC Magma trajectories: input bit 19,
    output bits 16..23. -/
theorem cell_19_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d7a4adeede0d544f73fcee2d69185014975825fc979c1d430589af8e#256) ⟨k.val, by omega⟩)
      (0x1a285d89#32, 0x0a8b58bd#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_19_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f517fad9f9b0b3c0e400d9982d15c14e602d09228cb6d328ffcb0000#256) ⟨k.val, by omega⟩)
      (0x593a1b37#32, 0x42d48652#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_19_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008d4777f95351c7d4e9ebf4de8318042221c32aedfaa5a3370eaaf0f0#256) ⟨k.val, by omega⟩)
      (0xd6a06b06#32, 0x9abf1473#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_19_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000efa90000290f4207c2afe564f5b8f608fdd8b34128b7a35332e70000#256) ⟨k.val, by omega⟩)
      (0x93e55014#32, 0xa46d8a28#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_19_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002e66fdffbd4fe34e60de677d231cdbbd07cc2c94ee04fe9f6de8ff80#256) ⟨k.val, by omega⟩)
      (0xd98d68ae#32, 0xed5991b8#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_19_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007895ffff5dbade53763c37332f130d4152baa07674f25c045ee6fdbc#256) ⟨k.val, by omega⟩)
      (0xc3c78e5b#32, 0xfed182cc#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_19_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ef8ff007fd4ebf2fc7631707f6d77d1979f0b1e85ca6c1f47900000#256) ⟨k.val, by omega⟩)
      (0xadc5fe38#32, 0x90f0e3d6#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_19_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000076ed00004c53ef1c4c64745957117f90b3c046e214aab19d01900008#256) ⟨k.val, by omega⟩)
      (0x97befc4d#32, 0x32f28e70#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
