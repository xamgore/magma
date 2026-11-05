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

/-- Kernel-checkable real RFC Magma trajectories: input bit 15,
    output bits 8..15. -/
theorem cell_15_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d2cd0fff69cb8d704f8e24ef50417d413d568e472df324865c7f86f8#256) ⟨k.val, by omega⟩)
      (0x3d0f451d#32, 0x76889a52#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_15_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fd36cfffe16097f78edb711b464117f6ed5261d7c77d16f897c475ff#256) ⟨k.val, by omega⟩)
      (0xa38f577a#32, 0xdffc5378#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_15_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d6d79fc49e368dd2c5bcf32847cdaf3fc04bfa2cf56780774e63a308#256) ⟨k.val, by omega⟩)
      (0x44a91978#32, 0x2b91ff27#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_15_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005e2714dc58f4239355cf046863d3e6ecb6df78a6f0be62018135de00#256) ⟨k.val, by omega⟩)
      (0xa69ee90f#32, 0x6544d37c#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_15_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000034cfd93edd31e9c86ae0c77f90b91ff8617ab2808c2d04f6cacb2de0#256) ⟨k.val, by omega⟩)
      (0x9ce0f635#32, 0x0179a6ea#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_15_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005e3e33d4bdae63dd04dbfa37b348ff7d17aa16caf2fdf34e08f16460#256) ⟨k.val, by omega⟩)
      (0x898ea335#32, 0x98879df8#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_15_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000050ecfff8717edbadebb061ea4b07adc8209dcbb3402bd0d985e137c#256) ⟨k.val, by omega⟩)
      (0x7ff67b36#32, 0x060baff0#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_15_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000042138f86adece80a78de8eaf6ed5dfb487aa26510bcdb53dd9cf6860#256) ⟨k.val, by omega⟩)
      (0x00b9e212#32, 0x77b52ec2#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
