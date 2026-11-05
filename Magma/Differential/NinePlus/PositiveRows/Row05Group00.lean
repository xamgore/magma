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

/-- Kernel-checkable real RFC Magma trajectories: input bit 5,
    output bits 0..7. -/
theorem cell_05_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a82ac0aef0220b6f34e4d903482c87613c2d117d83d90dfd045e4071#256) ⟨k.val, by omega⟩)
      (0xa42c0563#32, 0x8b67652b#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_05_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000221eae6f4cfabc321c857c5cf56ab41a1377b6f80c4b29db1c2e48df#256) ⟨k.val, by omega⟩)
      (0x27ecc190#32, 0x4ed259c3#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_05_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000558d69a0fdcbeb7ee92835929a0a8921e436cc26de8abb7b03b1c41b#256) ⟨k.val, by omega⟩)
      (0x14c570ea#32, 0x3ba9dff0#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_05_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e427f6efbcbe7d1a64a48a1f9e03d945d08e09807317fb35fdeea56b#256) ⟨k.val, by omega⟩)
      (0xae5bd79b#32, 0x3e73d8b6#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_05_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ec52e0f65b606202ab0eebacc0ce2daff7545f98417168c64d7d99b0#256) ⟨k.val, by omega⟩)
      (0x1e5589e2#32, 0x375393d3#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_05_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000eb5fe917025fe2c0182aaac0b32c408388b4b87838c9fd48a75cb830#256) ⟨k.val, by omega⟩)
      (0x89037ba8#32, 0xa735fb0a#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_05_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001fb58694c5c1d01a5a464e086d7b4d519fd2100832f4ad9a63428720#256) ⟨k.val, by omega⟩)
      (0xfb785a75#32, 0xb3c9aea1#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_05_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004cb7fe4ffc9ea325185a78ae3a878260d13e4f7ed829a1d41d2f8e7c#256) ⟨k.val, by omega⟩)
      (0x42915916#32, 0x09824226#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
