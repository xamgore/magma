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

/-- Kernel-checkable real RFC Magma trajectories: input bit 26,
    output bits 24..31. -/
theorem cell_26_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fe0000002fd11c6c9c6233bf0c65a6a4f228de443ec372c07f008000#256) ⟨k.val, by omega⟩)
      (0x6eea9c63#32, 0xd172b972#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_26_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d10000006f643358499dc3e69aff46113fe0b70122d20358a3f80000#256) ⟨k.val, by omega⟩)
      (0x1047e94e#32, 0x9a7cd9ef#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_26_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d30f800021de0e08d506ddcb3630e1b8c20727a3884e933dd9c97c00#256) ⟨k.val, by omega⟩)
      (0x45f66c4b#32, 0xc1d21a6c#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_26_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000edd00000b90dfc99b0fe99ab5a68cc5d237650bf65cbc1db4bf2400c#256) ⟨k.val, by omega⟩)
      (0x2103837a#32, 0x8d9b47b2#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_26_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000127a00005f25472b097efab5fa2a4e60bf00676c10f5d3abb00a0880#256) ⟨k.val, by omega⟩)
      (0x0a3eb417#32, 0xdd661ae7#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_26_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ccffc000fbe6dc470f0ba0ce2307d81fa4a30d9d9fef597e2ffff8f0#256) ⟨k.val, by omega⟩)
      (0x620a50e8#32, 0x22fed1ad#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_26_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000641f80005daf08632f794f6174d8e1f2c4172034ae22c11770d71800#256) ⟨k.val, by omega⟩)
      (0x7f7ad566#32, 0x56f88a19#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_26_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a600000047c935bada053c2092bc40481ed6eba70be395a020e77a02#256) ⟨k.val, by omega⟩)
      (0x404da9f0#32, 0xed57ef2a#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
