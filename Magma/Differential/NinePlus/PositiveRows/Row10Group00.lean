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

/-- Kernel-checkable real RFC Magma trajectories: input bit 10,
    output bits 0..7. -/
theorem cell_10_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005ae645825102026d4f51e75d5151526d01675741c4c3877c4565b6ed#256) ⟨k.val, by omega⟩)
      (0xce0227d8#32, 0x997271bd#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_10_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000855a4bffb8ee56863830ec732118ff53b04e414ad8adaacdc809b8c1#256) ⟨k.val, by omega⟩)
      (0xa0c7196d#32, 0xbab52c65#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_10_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000946a9dcfa21da08dd44fc93d88a445535804a0bcd6b9cccddc7d3632#256) ⟨k.val, by omega⟩)
      (0x9bc18001#32, 0xe8bb2c40#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_10_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000868ef72c5f289d0c1923433633d71eba72863ebb169b358c5dc8a9f5#256) ⟨k.val, by omega⟩)
      (0xe5c9df32#32, 0x17d7ea84#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_10_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a943feb0c97ba2cd4354d2b108bc1b726f6bcb3fe9c8aeef9c61d788#256) ⟨k.val, by omega⟩)
      (0xae885bdf#32, 0x92f7de16#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_10_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008fa03500049eedfb3678b38a45458945136c58defe14636a736fdea0#256) ⟨k.val, by omega⟩)
      (0x647a6b1f#32, 0x8918e3c1#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_10_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006bc3be50b67851bd8d0610737807a21e37b83c9d2ba0a3de31617756#256) ⟨k.val, by omega⟩)
      (0xe9dab0db#32, 0x4f7976d8#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_10_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fc9ac2ff3929d01683837317aae89a39416a07a05cf0077a25a775b0#256) ⟨k.val, by omega⟩)
      (0x75a251f9#32, 0x047a439a#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
