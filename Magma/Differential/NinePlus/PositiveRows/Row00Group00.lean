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

/-- Kernel-checkable real RFC Magma trajectories: input bit 0,
    output bits 0..7. -/
theorem cell_00_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000486095bee1b7f91f0eda9921cfa82cb7723eabd878c61ed23f259f7#256) ⟨k.val, by omega⟩)
      (0xcfc325c2#32, 0xb7e4fa64#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_00_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000866badbba042df7637b48fab5935cf8c54d2dfb874975b405faee9bf#256) ⟨k.val, by omega⟩)
      (0x70053ffa#32, 0xef2bf42a#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_00_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b8436ec55713a24945f9d8be6cb948ace11fb2b2d40c5373fc09a92b#256) ⟨k.val, by omega⟩)
      (0x135fc2bf#32, 0x1b46ec04#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_00_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c8586999ba6d2aeefac785623a01415809949bb6eea6cd08bfd524b8#256) ⟨k.val, by omega⟩)
      (0xbadc3a1c#32, 0x6837a0b5#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_00_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007c6a78414a31f427fb76492e2b0f2810a9efd86c619c36699bd2a157#256) ⟨k.val, by omega⟩)
      (0x6deb7026#32, 0x9ed904f4#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_00_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001b2f8d3f88ede5c81857592e1e895c0254637d48725d9845a6a54d1c#256) ⟨k.val, by omega⟩)
      (0x8cf4a508#32, 0x95529b44#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_00_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d9f54c85e00c76393acce119fae79b4deaccfcd8f6d5fb53b6d01ca6#256) ⟨k.val, by omega⟩)
      (0xbb71d24d#32, 0xf425a500#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_00_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003ab32499d3cc003e7243dc78eb6af17eb958635d08962d29fc4668d0#256) ⟨k.val, by omega⟩)
      (0x17c0f758#32, 0x6f1f5105#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
