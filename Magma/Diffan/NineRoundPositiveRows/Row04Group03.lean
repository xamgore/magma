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

/-- Kernel-checkable real RFC Magma trajectories: input bit 4,
    output bits 24..31. -/
theorem cell_04_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000153576d158f12b2cb789f129b33b23a1c7bf74019ef0a272ae0f7f00#256) ⟨k.val, by omega⟩)
      (0xd908c439#32, 0xa22ea8a7#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_04_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006d18464f2dd5c23de295d6934ae3f179c6f187ba47c8e7b9efffff80#256) ⟨k.val, by omega⟩)
      (0xf6aa6bd9#32, 0x87cf95c4#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_04_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006d7be9d0e7c9d99d5f3d24bb4d7bf70531f6d9f69627dbfafb013040#256) ⟨k.val, by omega⟩)
      (0x6490ceb1#32, 0x0e472346#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_04_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000043561e77bb20bfb69b410682804ea9e38775dcdc87efaa8f18341f0d#256) ⟨k.val, by omega⟩)
      (0x6892248e#32, 0xa6781ab9#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_04_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004c27d9b482598c8fd11a984e3dcedf36e4fafa13a084229bf0e77560#256) ⟨k.val, by omega⟩)
      (0x86fbcfdc#32, 0x7e18abba#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_04_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000907be40f6320d7e227a1f2b092f80bea33bf3cb2a4e2d4f1ff878fff#256) ⟨k.val, by omega⟩)
      (0xf044caa9#32, 0xf0b54384#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_04_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001fedd39779ac4513b08c61f2497f17a638829b95bf32d47dcff8fdcf#256) ⟨k.val, by omega⟩)
      (0xfa448266#32, 0xd2cdf8d5#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_04_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ffb2c7c5aaa6885729e7defec1571aa4145517902252132acfd815b5#256) ⟨k.val, by omega⟩)
      (0x1c9ba3e8#32, 0x1d9dc6dd#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
