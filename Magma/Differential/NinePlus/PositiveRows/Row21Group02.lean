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

/-- Kernel-checkable real RFC Magma trajectories: input bit 21,
    output bits 16..23. -/
theorem cell_21_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006329fcb57878c96280a6b88c9bfe608dbf34bf72fcf329d6493b180d#256) ⟨k.val, by omega⟩)
      (0xd40af1a7#32, 0x3c19ccd0#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_21_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000545000005cba8d3252d7c365b5420fe00d8316a2624f383157d60780#256) ⟨k.val, by omega⟩)
      (0xbc9bab67#32, 0x5d1ed2a2#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_21_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000042f00000daf261abe4f380e433f83606089cd34811ba4dd0c5e50080#256) ⟨k.val, by omega⟩)
      (0x86ea4def#32, 0xe8418df5#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_21_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005ad00000c8bae450a25562b075d54c8520ee67aa43c3a03df177c000#256) ⟨k.val, by omega⟩)
      (0xa13b091b#32, 0xa4241b11#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_21_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007fb0000050cacdf381387fc3c033d3d1c5148338f261140148840000#256) ⟨k.val, by omega⟩)
      (0x727e413b#32, 0xf95f5a10#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_21_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000e9000001f3120ec148ab63ca073cebf888f9a090b4b1b6049f00300#256) ⟨k.val, by omega⟩)
      (0x9249c6e2#32, 0x371e51a8#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_21_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003270000036e8edbbebc33ce5758818435b0214ac4c57db95f9420000#256) ⟨k.val, by omega⟩)
      (0x42dae639#32, 0x10b1d5a1#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_21_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d2dfc000307f507300338bfe070c24f4c5a322f56fb266f068510000#256) ⟨k.val, by omega⟩)
      (0x8275ad97#32, 0x395e2cce#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
