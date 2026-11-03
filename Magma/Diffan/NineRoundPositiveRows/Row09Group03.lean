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

/-- Kernel-checkable real RFC Magma trajectories: input bit 9,
    output bits 24..31. -/
theorem cell_09_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e13663de7fe6999a1ffe6024806cfc35f53a2a55e343e0d18ef18245#256) ⟨k.val, by omega⟩)
      (0x31420427#32, 0x4925b9bd#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_09_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000868148fecced044091055462ab10f8a589f1b698b45bc2115aa6b80f#256) ⟨k.val, by omega⟩)
      (0xae2d0950#32, 0xcc7ba6bb#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_09_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000020311d4e308eeafa26b0da3b58a574ac36ce3eef70113379fe580389#256) ⟨k.val, by omega⟩)
      (0xd3078752#32, 0xc7c5ed20#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_09_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001f5ea27ff81bdc835e1a31742e1fe6b6d4bd186aed5359ef0abd0003#256) ⟨k.val, by omega⟩)
      (0x6ff0c4f1#32, 0x7b59db3d#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_09_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008030e6ffa9b7fe46adb0fd6b71e7417d35ada757d45fcc4653ffff8f#256) ⟨k.val, by omega⟩)
      (0x46655550#32, 0x25b842a7#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_09_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003314f1fff0ec8483083976fdb5367278ff75db32ef70bb6b90fa3ffc#256) ⟨k.val, by omega⟩)
      (0xf5ae296f#32, 0xcb0c5651#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_09_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008800090043172b546516bc25464643fd8307230a7346a96d5c000080#256) ⟨k.val, by omega⟩)
      (0x02888432#32, 0x17da4398#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_09_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002d3ef5fe0b5b69ff0d8fa8275b37dcdefc14a857581349d1dda254b2#256) ⟨k.val, by omega⟩)
      (0xad6db830#32, 0x0bcaf742#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
