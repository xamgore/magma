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

/-- Kernel-checkable real RFC Magma trajectories: input bit 20,
    output bits 8..15. -/
theorem cell_20_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b3f08000a2c2f64ddd10c06270da68ccbe1fb11546ed5800f9d387c0#256) ⟨k.val, by omega⟩)
      (0x1e8fc134#32, 0x96eeb45c#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_20_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008eccaf0280f97beef3efdac4712811fa880e1ec8427899e8c7dae5d0#256) ⟨k.val, by omega⟩)
      (0x99d2e4ee#32, 0xf2e13c45#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_20_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cc4fffff7d43b361cc1d294207a12cb13de6f41c95feb547cbf16bf8#256) ⟨k.val, by omega⟩)
      (0x8d773135#32, 0xca1c43b2#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_20_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090c7305ec4a340c2ac8e1821ea3b50be05ff633b1c1264f1f721f880#256) ⟨k.val, by omega⟩)
      (0x11ba47be#32, 0x8e67448c#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_20_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004848000048d792383a44cc6e8b749f39bb91074710641f76414aab00#256) ⟨k.val, by omega⟩)
      (0xac07b5ae#32, 0x0e118adf#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_20_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b98cffff52064ec154a208ecce8ffa329b2711c121fe69924056dc40#256) ⟨k.val, by omega⟩)
      (0x99fe3773#32, 0xfcb03f4e#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_20_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ecfff7f9fe4b10a6dd0c0003de9078d493775634d3aebd6a519cfff#256) ⟨k.val, by omega⟩)
      (0xa4213ce1#32, 0x7fcda4be#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_20_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008d7ed9faa19005c9d051146c535281c05c070f980b0113fd3be57402#256) ⟨k.val, by omega⟩)
      (0xd7c0af4a#32, 0x191fa33f#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
