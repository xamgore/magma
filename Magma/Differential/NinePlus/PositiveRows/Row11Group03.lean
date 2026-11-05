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

/-- Kernel-checkable real RFC Magma trajectories: input bit 11,
    output bits 24..31. -/
theorem cell_11_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000aea219ffa7de12c490298cb608fd200144d1fe066b106b7184f6fffe#256) ⟨k.val, by omega⟩)
      (0x6f26a521#32, 0x3cca0507#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_11_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fa9ad0dede3877dca74b23120882672be4d893a598766dc685ce3010#256) ⟨k.val, by omega⟩)
      (0x93903406#32, 0x1723e353#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_11_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005b8999002c423862d831f7ff2a925225788d2294a9f1b8e287000000#256) ⟨k.val, by omega⟩)
      (0xb2980b98#32, 0xef6cd01a#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_11_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000604d54ffd1cb30dbfa0bec5257b8192b4870683e37c4164ff9fffff0#256) ⟨k.val, by omega⟩)
      (0xbc66a3f6#32, 0x4bcf6b1c#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_11_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009bf5eeff02f97fc8560bbe3c1eb14544b41413f0d0498406efb90cff#256) ⟨k.val, by omega⟩)
      (0x116cb52c#32, 0xe1c09cd5#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_11_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006ba8b900acd65cfaea5a9fc3a178862d285e84853602b41bb0bef800#256) ⟨k.val, by omega⟩)
      (0x5bd5b3c3#32, 0x818c6f6e#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_11_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006e4408ff3806158dc54bb1483d5626fb85293b11e3ee1b3acfffc0f7#256) ⟨k.val, by omega⟩)
      (0x4696ae90#32, 0x0c58d956#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_11_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cb8a95ff71161abc0c993a36bcdae651867799804879c22acc98faaa#256) ⟨k.val, by omega⟩)
      (0xf8a00408#32, 0x42978b5a#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
