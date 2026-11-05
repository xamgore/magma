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

/-- Kernel-checkable real RFC Magma trajectories: input bit 15,
    output bits 16..23. -/
theorem cell_15_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5a56fffe1a4250613d7f05fe77b7d60efa08cd3d61718b7fb3aff80#256) ⟨k.val, by omega⟩)
      (0x0f134966#32, 0x3b36ad25#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_15_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000095c01fff7d2e1abff906e1d9c71c0b710f4b5f77e768a623475f000f#256) ⟨k.val, by omega⟩)
      (0xd1ccffcd#32, 0xcbd12e03#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_15_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000017c97fff7b9b50d9e26599bac860a147d4a2e905882a93a2f80b838f#256) ⟨k.val, by omega⟩)
      (0x6d91d7a2#32, 0x65760691#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_15_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c6c48ffffea86599ecc6dcfea2577d4e82b13935d023c56223f7dff8#256) ⟨k.val, by omega⟩)
      (0x6aed4c76#32, 0x2af686d4#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_15_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000dfc23ff5a4d4d0eebdf8c316e84eb4b651f6f4fba4053dbbc36b15e#256) ⟨k.val, by omega⟩)
      (0xa9c380fc#32, 0x43e983ea#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_15_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003bed3fc2e9949a044315f5941e6c3dbc8b1e96723f1af3b20c6c9280#256) ⟨k.val, by omega⟩)
      (0xd4e4be62#32, 0xbe20b8de#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_15_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bb7d3dfb4c95fbb0e7416e73dacb81a66b452c19d277ded3f3d0ccf0#256) ⟨k.val, by omega⟩)
      (0x88a3ac97#32, 0x02a51b2a#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_15_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f3724fff7fd2109d871e98dbc92bcc59aa9cee07a7b3eb054179f80f#256) ⟨k.val, by omega⟩)
      (0x0531bf2d#32, 0x9610ca46#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
