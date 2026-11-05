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

/-- Kernel-checkable real RFC Magma trajectories: input bit 12,
    output bits 8..15. -/
theorem cell_12_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d1bdcd441e7131c07d1572260374701b2edae2d148f9ae2e97cbfe80#256) ⟨k.val, by omega⟩)
      (0xac3deca8#32, 0x829695f6#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_12_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005fe9b77e5624b8c464d3cc2a3618265196432f9a23c97c27bafcf1a8#256) ⟨k.val, by omega⟩)
      (0xd53ba5a3#32, 0x763212c0#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_12_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000a06cf7f8b90a3a77615c33043095e4c1d9d6c3f73624fa1c43ba4f8#256) ⟨k.val, by omega⟩)
      (0x268b49e7#32, 0xc1a678a0#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_12_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c1c8aff1e11c59edfe102f2f24841a354120348a92b392aadf8e9210#256) ⟨k.val, by omega⟩)
      (0x26febe10#32, 0x93046d38#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_12_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c88a2fff8268ec917b9a62f66a141373eb296cd484b07009cfd6afff#256) ⟨k.val, by omega⟩)
      (0xe7f65a3d#32, 0xc8bd3fbd#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_12_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000037fcaf7ff29aa71ed5ca2c0cc7d377ed598bb21ea81a69187727d8f8#256) ⟨k.val, by omega⟩)
      (0xf4c6a6ba#32, 0x7c7b83c0#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_12_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bd4b0f0021ea08adf2d808419d6c4b06e4f22e2aa71dbcfb408cb57e#256) ⟨k.val, by omega⟩)
      (0x6430242d#32, 0xa413a649#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_12_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000650ef3f5655d67c26482b4c6ccae6df6da515ca784e5642047b5ff8#256) ⟨k.val, by omega⟩)
      (0x11668d59#32, 0x1892ed33#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
