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

/-- Kernel-checkable real RFC Magma trajectories: input bit 30,
    output bits 24..31. -/
theorem cell_30_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050fd0000b5a13f4d57c0b4eed5f246bafb7480271222e3a9a88647f0#256) ⟨k.val, by omega⟩)
      (0x50a5df98#32, 0x3593d373#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_30_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007dfb00002a5ada1f6efde00fbeb0c2a90de28c9405f6624f00040900#256) ⟨k.val, by omega⟩)
      (0xe2222399#32, 0x4b8223a5#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_30_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0009000222beaefa98b10c7ead6d03915d0261ede11a3ffeb180080#256) ⟨k.val, by omega⟩)
      (0x0868a24f#32, 0xb15de89d#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_30_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b800000040bcf3003d88ef66207b1faabab87cc7c493ec6b9d8b6500#256) ⟨k.val, by omega⟩)
      (0x49b5ab5a#32, 0xfbfe6170#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_30_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b8000000b3841d00f9e4861482fb9125f5d7f2facba00527400000b0#256) ⟨k.val, by omega⟩)
      (0xc5592272#32, 0xd01a335b#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_30_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000060000000d889fce0134d03f389a2900452480a02cbbab2ca30000000#256) ⟨k.val, by omega⟩)
      (0x4e5b3397#32, 0x641c2721#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_30_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000100000008f606f63803a81c6067a649efd762d9ba993615c40650000#256) ⟨k.val, by omega⟩)
      (0x52c8c48d#32, 0x25ba3e0a#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_30_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e00000004c464afdd3fb480b45aba072ff65e13155597090f86ebd69#256) ⟨k.val, by omega⟩)
      (0x81e9e005#32, 0xda6c8dbc#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
