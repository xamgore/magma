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

/-- Kernel-checkable real RFC Magma trajectories: input bit 24,
    output bits 16..23. -/
theorem cell_24_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cc3ffff3a0f6b0e649c323282cced6b4c60dae8afe22faf3280d860#256) ⟨k.val, by omega⟩)
      (0x1bc387ef#32, 0x3b9a2870#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_24_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000170800007a4d06d02ac702ad0136025a7a38980c3d70124553e30000#256) ⟨k.val, by omega⟩)
      (0x0a1b62d9#32, 0x234d53ad#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_24_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a5008000422417917c6f34161105200c4ba55a8ad01b3002ea8a0000#256) ⟨k.val, by omega⟩)
      (0xda13e985#32, 0xfb032375#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_24_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f7243fff6aac3a89458d3f6443d58887d4e75db9084b67c2471ad2f0#256) ⟨k.val, by omega⟩)
      (0xe8b03fc3#32, 0x54ad9cfb#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_24_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000650800007dae438b20f8ee7f831014c5f70db0615dc6de12023000e0#256) ⟨k.val, by omega⟩)
      (0x32865292#32, 0x74e0916c#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_24_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bac00000811d2c1296188262420b43f2785c6f8268e11fddb8300000#256) ⟨k.val, by omega⟩)
      (0x33930248#32, 0xf6c6653d#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_24_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000510800002d16e8e43237d55d64e5aa079342f0fed805d90e79f5f204#256) ⟨k.val, by omega⟩)
      (0x71b02135#32, 0x3b02d9f0#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_24_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000058808000f530641a8e4cab6e647d265767c397f0a44c4598ff400000#256) ⟨k.val, by omega⟩)
      (0x8120b2ac#32, 0x63ff4925#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
