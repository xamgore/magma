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

/-- Kernel-checkable real RFC Magma trajectories: input bit 21,
    output bits 0..7. -/
theorem cell_21_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003fc00000dd7ea0d145976500e6402034d61fdf7ad0ddc1fb01627109#256) ⟨k.val, by omega⟩)
      (0x7b84445f#32, 0x808531bf#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_21_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0ca3df08c4d03b8b11c97e00b95dea065255addc8bb46b870d9bf15#256) ⟨k.val, by omega⟩)
      (0xd42837fe#32, 0x71d5743c#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_21_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d9dfffff6033c5ad75844a9a5c76f750acb0dc87140a71aba56c2035#256) ⟨k.val, by omega⟩)
      (0xc51a6d16#32, 0x7fae7f72#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_21_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000361ffd794abb04cd06d17e33fdff5e3440a4004cec87e12ae14c95e9#256) ⟨k.val, by omega⟩)
      (0x9bdb950c#32, 0x965352b6#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_21_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000097efffff36421a855065fc74ab6817172aaddc34c96a5efec4f17108#256) ⟨k.val, by omega⟩)
      (0xcd401dd7#32, 0x16e8accb#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_21_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f749b10dc2d49dbff5fc71eb9b5f82be9addeea4481c8fe3e21b57de#256) ⟨k.val, by omega⟩)
      (0xfb4a905d#32, 0xcf64851b#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_21_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e71fffff1cd4d91b2876638b49614becea5fd44309dffbd36049fc9d#256) ⟨k.val, by omega⟩)
      (0xd7fe13a0#32, 0xd855d473#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_21_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000073b00000f8218c6004b52fe42bec143047c821c03a14e7837fc988c0#256) ⟨k.val, by omega⟩)
      (0x68b8f80e#32, 0xfdabe8f0#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
