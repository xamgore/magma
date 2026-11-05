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

/-- Kernel-checkable real RFC Magma trajectories: input bit 19,
    output bits 8..15. -/
theorem cell_19_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006477ffffea04720e69e2fe0d6478191adb6fcd97e366dfd27de9fd87#256) ⟨k.val, by omega⟩)
      (0x4c94c463#32, 0x3d7ed427#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_19_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000039cffffd61c398ec7ffb1b83fc5d7d9a0d4f32fabdcd4999e8d51fc#256) ⟨k.val, by omega⟩)
      (0xb473f29b#32, 0xb65a94b7#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_19_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f035ffff4b15d6dd2d75c2e93349f7246c6980c7f4d7a54ee866f9fe#256) ⟨k.val, by omega⟩)
      (0x03abdfcd#32, 0xb92fb924#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_19_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000052e70fffb56cd06d659940ce1f32b616efc62021ef88bd43d752594a#256) ⟨k.val, by omega⟩)
      (0x4f945b22#32, 0x07f68b2d#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_19_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000511d0000677b64e4c65944ee6a45654834808641683eabd188003000#256) ⟨k.val, by omega⟩)
      (0x1797f1a1#32, 0x73faa99e#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_19_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000063a5fffffeef56594c4b4845abda91c7cb7ff2972bc5e2a32a012fe0#256) ⟨k.val, by omega⟩)
      (0xc044ea23#32, 0x5fa711a1#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_19_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000611cffff9c38e11f61fa8ddc6e9730dd87ce2ba7b99e1c67b03c2c00#256) ⟨k.val, by omega⟩)
      (0x248196c3#32, 0xaf90d7b5#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_19_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004ed7fe2ffd231b5e3ca3d8f541826e55dc61ab5ec1f621a653629ed0#256) ⟨k.val, by omega⟩)
      (0xabe5aa9b#32, 0xba5b43cb#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
