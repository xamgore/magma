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

/-- Kernel-checkable real RFC Magma trajectories: input bit 29,
    output bits 16..23. -/
theorem cell_29_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000000000000d2ba3dad179f6765b271cbaf2cd0eeab59cec3bc75c68000#256) ⟨k.val, by omega⟩)
      (0x35430a84#32, 0xaffe4095#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_29_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001017b0005f1161fc054f64ab46fcb968e8108c8bc2cebbbcbecd66d0#256) ⟨k.val, by omega⟩)
      (0xc252fffa#32, 0x4ca9c132#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_29_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005c000800e338fa7c2701e09086be9470968cf83b3f548048b67c8500#256) ⟨k.val, by omega⟩)
      (0xf150b9de#32, 0xed540dd9#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_29_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dcff800070eed63d4b9f25ff7b923d1ad5f6b8a1efac8e1b5218fef8#256) ⟨k.val, by omega⟩)
      (0x53120e84#32, 0x950dd6c6#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_29_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000200000005c1c323fba5ef282bddb26faa4eb45256c5dc00ce54e0004#256) ⟨k.val, by omega⟩)
      (0x1577c738#32, 0x73b4af24#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_29_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000700e00009d2e0c2b01bbf7652444f38d558e75db07db119091b00000#256) ⟨k.val, by omega⟩)
      (0x94ed08ef#32, 0x1cf2b99c#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_29_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000030877e00f7fbf48386021b7cfd7a09ec160cff137a41acce683f7005#256) ⟨k.val, by omega⟩)
      (0x7d39885e#32, 0xb79d962b#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_29_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7ffc000728acc6ee7bc35614907b6cdc023babe7fab0252c470cc00#256) ⟨k.val, by omega⟩)
      (0x5161aaa7#32, 0xaa1af4ce#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
