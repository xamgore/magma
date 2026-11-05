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
    output bits 24..31. -/
theorem cell_10_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bbb69a7f12e0f693d47cbd4aa5cbe78f64d5126e9cd10c4d310270c4#256) ⟨k.val, by omega⟩)
      (0x8d1fe337#32, 0xfa2126dc#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_10_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000da2c347f597ccbf27934a8d946abd90e43b719d713efa46326efff80#256) ⟨k.val, by omega⟩)
      (0x5f72f92b#32, 0xa532bb22#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_10_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ebf93b00cc09b95c6a04f5167a35112491fc9fa280e5c9a4abf00000#256) ⟨k.val, by omega⟩)
      (0x1f0eb9ff#32, 0x42ec79ee#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_10_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008a625aff15c65e6b83e29b16ef0712fe82068379f85b6431fbbae9c0#256) ⟨k.val, by omega⟩)
      (0x1a38fbe8#32, 0xd6da2856#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_10_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000879bcbff827d51b1258dd710124bde8659651350944bcd75a1888707#256) ⟨k.val, by omega⟩)
      (0x67afb50e#32, 0x528900bc#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_10_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ed4698ff93dfb31034c9ca3ff35dc7fd85d7b6b80cf9f3be300c9833#256) ⟨k.val, by omega⟩)
      (0x7d485c03#32, 0xb762682b#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_10_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e8b9d300116570044cd1b641950ab697210815aa0e1433e038000000#256) ⟨k.val, by omega⟩)
      (0xb20b85e2#32, 0x07c4f1c5#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_10_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001b9dafffa41285884a8ba4b8fa39167ee8661b7fe3278989ca14662c#256) ⟨k.val, by omega⟩)
      (0xf7fae3a7#32, 0x2165ff60#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
