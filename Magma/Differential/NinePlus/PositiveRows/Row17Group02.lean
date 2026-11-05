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

/-- Kernel-checkable real RFC Magma trajectories: input bit 17,
    output bits 16..23. -/
theorem cell_17_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000edaffff5ab7004918c4053be36abc7314e1f458797e6139c90f007c#256) ⟨k.val, by omega⟩)
      (0xfff72854#32, 0xaf2ae607#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_17_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000059923fff7b720a04ee5f4364962b850c220b61405eba7df8b2de2fe0#256) ⟨k.val, by omega⟩)
      (0x38e889ff#32, 0x422c4f7c#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_17_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001441b42f1acf1e7f633658d0594cdcd78037d448a4973eadb8eda0e0#256) ⟨k.val, by omega⟩)
      (0x9132d46b#32, 0xe920b94b#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_17_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002f3f0000b0331415ceafa1744625c8340f882b51f0b65e013ad30000#256) ⟨k.val, by omega⟩)
      (0x7cae7d1d#32, 0x66cb7741#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_17_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004cfb0000f5e6257d89df65ff5f03aeeae57e863ee755de78ce8f8000#256) ⟨k.val, by omega⟩)
      (0xf2c13c62#32, 0x70c383fa#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_17_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004bcb0000d418f8222af1607a07a94acd6d1b9ca0c0487f4431d00000#256) ⟨k.val, by omega⟩)
      (0x039fa668#32, 0xbdef7ab0#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_17_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e29a4d0991b7166d36b707ea9ce92a573e8ba1a62d15b631f6309000#256) ⟨k.val, by omega⟩)
      (0xf1216b88#32, 0x3773d3fb#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_17_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000026ed00007c8404769c08755b8c57f67fbab0829d93df77aa93900000#256) ⟨k.val, by omega⟩)
      (0xdc341e85#32, 0x6254ab5f#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
