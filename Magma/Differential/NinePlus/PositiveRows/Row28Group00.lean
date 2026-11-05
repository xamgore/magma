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

/-- Kernel-checkable real RFC Magma trajectories: input bit 28,
    output bits 0..7. -/
theorem cell_28_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000080000007b079dc1fba95b835af17d255938e195251d052da12fe5e5#256) ⟨k.val, by omega⟩)
      (0xb46c636a#32, 0xdfe54c3b#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_28_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050000000582c257c9a57034cbe1efcecbe93ee807e0f6eb7779c922b#256) ⟨k.val, by omega⟩)
      (0xad13a40f#32, 0xe75ba621#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_28_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f00000006f28f27d09f67416159415c6118dbde71cbf8250e5a4e844#256) ⟨k.val, by omega⟩)
      (0x1c39cf7f#32, 0x6c132c8f#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_28_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000541e701cec7f3f2da69eacdacf85e93394016ff57cdc065073ca5507#256) ⟨k.val, by omega⟩)
      (0xf83319ed#32, 0xd900ff94#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_28_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f08832007a7e51ae3c7cc30b6e0f14955fad54f855215b9dbd26faf0#256) ⟨k.val, by omega⟩)
      (0x5caf8482#32, 0x244a730d#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_28_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002e000000f2d32af00f4d518494467899eae7ee5ba819c29e7ee105b0#256) ⟨k.val, by omega⟩)
      (0x15b7446f#32, 0x268e62b7#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_28_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005003e000ab615aeb4a5a57e7c8cced1012a6be18e9d4967e7ef9be30#256) ⟨k.val, by omega⟩)
      (0xd21f8c21#32, 0x25dc53f5#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_28_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ef8300006a4a95ba1401f44a6014f13d26bc9fa25e461dc04819ddf0#256) ⟨k.val, by omega⟩)
      (0x81f04c5d#32, 0xf94b2a55#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
