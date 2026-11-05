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

/-- Kernel-checkable real RFC Magma trajectories: input bit 9,
    output bits 8..15. -/
theorem cell_09_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000693e90c0693f4be57a3af33681d06fdd283af4dda5b0dbc9f290ad7b#256) ⟨k.val, by omega⟩)
      (0x9dd9caf5#32, 0x20df1181#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_09_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000902ada005db7745746ff83c05d13b20ec0654dad7e8e88f7dce09920#256) ⟨k.val, by omega⟩)
      (0x3cd6ad94#32, 0x8425abbf#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_09_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ff6472ff49ff6e31e07d741b11872faa738690849bf3c1e6be83edf8#256) ⟨k.val, by omega⟩)
      (0xe4e9a4a9#32, 0x48e3a8a5#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_09_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c52205bc64982c663ba300e7c303eed1e5f9d04fcbc9c460e3b5390f#256) ⟨k.val, by omega⟩)
      (0x0978ed7b#32, 0xeff48b53#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_09_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004111e8ff73e2f4a232c6eeff56b10effb81ab5ac02324f4b44cc2f7f#256) ⟨k.val, by omega⟩)
      (0xb4025a06#32, 0x9fa33717#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_09_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000507cb9ff0a005fe6df8b262afba970a8b98ab0b7d1905bbfa3bb63ff#256) ⟨k.val, by omega⟩)
      (0x85d93650#32, 0x7a5050a8#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_09_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fe6d062b4426788912ef65ae3c8428fe9f9c5650ee7a30cd24461000#256) ⟨k.val, by omega⟩)
      (0x814b5c96#32, 0x9b9d6031#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_09_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005dd3166192c8e61aca43be67fa96bac8d2e818c4eb4b137e6db92cfd#256) ⟨k.val, by omega⟩)
      (0xc212c1fe#32, 0x041d9a75#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
