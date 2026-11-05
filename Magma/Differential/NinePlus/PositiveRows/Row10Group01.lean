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

/-- Kernel-checkable real RFC Magma trajectories: input bit 10,
    output bits 8..15. -/
theorem cell_10_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a9308b00cceee5ba82b4d435df6028030fb92ceb2150015fb70b2b00#256) ⟨k.val, by omega⟩)
      (0x8c6b188d#32, 0x9f45bb1a#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_10_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d6c5a40fdac5bff32974e991c40754e56deade7fd0f6dbdd6c4eb1f8#256) ⟨k.val, by omega⟩)
      (0xd05975a3#32, 0xa062de05#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_10_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009299baff8c1e035fc35591ad8a19df37090fb9e3463aa67a45192d00#256) ⟨k.val, by omega⟩)
      (0xee634503#32, 0xd079c35c#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_10_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000211037729093bacbf35965deab35b654908d5e32f12c42526a3fb434#256) ⟨k.val, by omega⟩)
      (0x09a80d72#32, 0xe86c53f9#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_10_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003e7544ffbdc8105edd63610979ccb87e1f4b5983fbd9d868612c898f#256) ⟨k.val, by omega⟩)
      (0x291d1a40#32, 0x942e06f1#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_10_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001c2ae2ff4d32bba06730ed00c76b8f1fc17b57ca1fe6db340fa06fc7#256) ⟨k.val, by omega⟩)
      (0x0f83028c#32, 0x7f82167d#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_10_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a1e6a1007bd52a8efc821a25de6d76d791bcffabab4b012ad96cb000#256) ⟨k.val, by omega⟩)
      (0x1bd6932a#32, 0xc4a4edf7#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_10_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f51d93ff1728c14db49033f91745f5fadfac591971c1b59528538ff8#256) ⟨k.val, by omega⟩)
      (0x74302e4b#32, 0x8bfde6a9#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
