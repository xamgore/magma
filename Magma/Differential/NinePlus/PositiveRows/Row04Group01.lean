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

/-- Kernel-checkable real RFC Magma trajectories: input bit 4,
    output bits 8..15. -/
theorem cell_04_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d8ff8030cb8cbd54cd3a348819414dbbf492e6e27105eb83a225d0ff#256) ⟨k.val, by omega⟩)
      (0x5075cf0e#32, 0x0adad8c2#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_04_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000077a53aed1668fa7d2535de1fa2643809e5d96f1fed8bb674c58797a0#256) ⟨k.val, by omega⟩)
      (0x37355ece#32, 0x1a71d7fd#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_04_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007eea47bf4457009f86c60e1ce5cdf9b414681844f50535fda857fd0f#256) ⟨k.val, by omega⟩)
      (0xc74b1db2#32, 0xe1cb87d1#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_04_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b356466f9581889ca3ea99d41164766dcaaf3712b6a2f7e1c6b76ef8#256) ⟨k.val, by omega⟩)
      (0xfbdc1d68#32, 0xc70128c1#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_04_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c36c70502c924d7eb598f2ab720ae1e726e4fa73d89308937a0287fe#256) ⟨k.val, by omega⟩)
      (0x5970e214#32, 0xef94fc0a#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_04_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008e40f5af0a81028d2760723febe86bafc27a47983f501e24ebabe00f#256) ⟨k.val, by omega⟩)
      (0x1a5f4119#32, 0xb5b7bce7#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_04_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d8b5211771a61cadee4358ad902412757b1c479099169d8ca181b900#256) ⟨k.val, by omega⟩)
      (0xf985b85a#32, 0x34074d90#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_04_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090ed0aee89691f236e78b48a3db9f9ed109c0a645216e4172d09b050#256) ⟨k.val, by omega⟩)
      (0x21b8d339#32, 0xd38242a1#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
