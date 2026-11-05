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

/-- Kernel-checkable real RFC Magma trajectories: input bit 2,
    output bits 8..15. -/
theorem cell_02_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e0e538967dfd7017c3434d686b570182404418f2aa34d7f1e4519900#256) ⟨k.val, by omega⟩)
      (0x674d11f0#32, 0x3e50e6f4#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_02_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dce109f6d5c30d1f19a099680e5c9985a591916af371637d6145f300#256) ⟨k.val, by omega⟩)
      (0x7c155016#32, 0xdec0d9b1#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_02_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000035be5e943f48782cc60b4be742fdd3a7f17fc1a279256a45891613b0#256) ⟨k.val, by omega⟩)
      (0x762623f9#32, 0x52a71cfc#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_02_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000870151ac1f57f8c889f6d2f5b9afb756867def5435fa29fbaf528efc#256) ⟨k.val, by omega⟩)
      (0x6c92c0cf#32, 0x3ed3071a#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_02_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001a6bd47b83472d2231e62919f8d05c7cae6b7b04bd618849c13f508b#256) ⟨k.val, by omega⟩)
      (0x9ae2553f#32, 0x3fa7d87e#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_02_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000068ce9095f89f2718cfc9cb3ec34a8b229d26d0dfd4b4b32c6ff663ab#256) ⟨k.val, by omega⟩)
      (0x543e2303#32, 0x6c7d8997#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_02_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000048199e44157e85e4653c07b4aaeb9ddf4875e2f1e0dee85f2df3afe0#256) ⟨k.val, by omega⟩)
      (0xec4ff1a0#32, 0x4e7c8033#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_02_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000079c8cf5d90dca01ad2fa434564a0a73c1b839e502e2d03dee5327cff#256) ⟨k.val, by omega⟩)
      (0x47dd1e5e#32, 0x380f37a5#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
