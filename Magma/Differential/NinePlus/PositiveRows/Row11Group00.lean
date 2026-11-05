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

/-- Kernel-checkable real RFC Magma trajectories: input bit 11,
    output bits 0..7. -/
theorem cell_11_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ccae900141b207bf0d104f45fa729e609a8da13bd19f581b6c9e29b#256) ⟨k.val, by omega⟩)
      (0x96251d8f#32, 0x194da4ec#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_11_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a5fc4f8ddf2f82bacc784f3e118197beb52b8c308590a110976bcee#256) ⟨k.val, by omega⟩)
      (0xbff78157#32, 0x535bd6fb#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_11_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003021d7ffc7981fd73fa3090ebcbd5f24f6fd1b347477533d1fd81c9e#256) ⟨k.val, by omega⟩)
      (0x53dd0bf4#32, 0xc01a2f05#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_11_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009a660c78c726be7d5b0acbf465e2d60be7f2143e19a6e29d411cefa6#256) ⟨k.val, by omega⟩)
      (0xadc7ef4e#32, 0x61b1907d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_11_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cfe9dff207b6e0cd7797a02ef75d6124827c416287e700593e93bef#256) ⟨k.val, by omega⟩)
      (0x8cc8ff9d#32, 0x30d9413d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_11_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000074de19fb92b78d88a1b4ff4ec9f8f918b80507b08118f4f5b107ce18#256) ⟨k.val, by omega⟩)
      (0x59aca58e#32, 0x00c3b959#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_11_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008c3f22fe3e149692010cb436d943302080eedd58cb9ad1f4b5152b9b#256) ⟨k.val, by omega⟩)
      (0x7c3c47be#32, 0x5168654d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_11_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fd2767ff00244ceff46dbb83456e8039065610328d0145395710d4d0#256) ⟨k.val, by omega⟩)
      (0x70c4e074#32, 0x34d4511e#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
