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

/-- Kernel-checkable real RFC Magma trajectories: input bit 26,
    output bits 0..7. -/
theorem cell_26_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004a00000096efb489a002cbf7b06b0cac29c27b7b4b2fa56c2d1d6943#256) ⟨k.val, by omega⟩)
      (0x4a4d7b3e#32, 0xfce2eb3e#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_26_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000214fffffda4324154d4408244543700ed06f989721738be4005f5f1e#256) ⟨k.val, by omega⟩)
      (0xb9af8091#32, 0xcd5d52db#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_26_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000db8fd5c409e1983eaa05c0be561127827ce5614352bbfe5cf31dad25#256) ⟨k.val, by omega⟩)
      (0xc8f39eb9#32, 0x9eae24b8#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_26_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000aca240089609ee8b7f08e74c26141b6011cfa40334ae3079580d9fa5#256) ⟨k.val, by omega⟩)
      (0x596071c2#32, 0x84d1aa57#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_26_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d90d0500061e1c36a806cc177f505507b1db911d38ae69d49049ef13#256) ⟨k.val, by omega⟩)
      (0x5edbffb3#32, 0x777aaa84#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_26_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000078213c6845e745d3e8ff1c4fae7da4bb9716349e7053c5a6fefadb30#256) ⟨k.val, by omega⟩)
      (0x2b74649a#32, 0x26773265#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_26_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000be8307fd1abc11e58499c44eaad08989fc58c75faf34b18618d14cda#256) ⟨k.val, by omega⟩)
      (0x0761fd96#32, 0x29f87a1d#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_26_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000132fffff34ee9c9857129a00e1478b7042c45e37be844858214a705f#256) ⟨k.val, by omega⟩)
      (0x053997a1#32, 0x64d1e8b8#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
