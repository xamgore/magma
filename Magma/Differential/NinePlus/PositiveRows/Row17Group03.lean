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

/-- Kernel-checkable real RFC Magma trajectories: input bit 17,
    output bits 24..31. -/
theorem cell_17_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f6ed800011cea94b8c7ba5fc842c6b9207bdb6005a41636b9d080000#256) ⟨k.val, by omega⟩)
      (0xc175a68d#32, 0xa3e2637a#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_17_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fa29fffce2a183cc64ff113f93933ba0f9dea144e770349ba095c000#256) ⟨k.val, by omega⟩)
      (0x7539edb5#32, 0xec6837f2#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_17_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006d220500cc9672f27ffc952bbf15a0d1a425b2db74ac44d0a1412010#256) ⟨k.val, by omega⟩)
      (0xde34d057#32, 0xa671e70f#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_17_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000426cffff7025734b264bb0003a01acd4ace622eae6352aa019c06000#256) ⟨k.val, by omega⟩)
      (0x1e68cace#32, 0x4d6f8533#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_17_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008bd67dd8ce378e6f55d87612aa2786d540c762ba488fe154260d70c0#256) ⟨k.val, by omega⟩)
      (0x6245ccfd#32, 0x5a9f4a51#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_17_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008c15000007f2cccf65dead8e2ae6553844753f6d6aa2a66400000800#256) ⟨k.val, by omega⟩)
      (0x6bd660d2#32, 0xce2a5afa#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_17_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000047e38007b37754a2c231299601815ee5afe8cb4a26394a4f82ba000#256) ⟨k.val, by omega⟩)
      (0xf55a87e0#32, 0x3891402d#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_17_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000fab00004f74b3376b5ffd107c451bfeedb02b24ac340c802d465fc8#256) ⟨k.val, by omega⟩)
      (0xba36a234#32, 0xd1755ce6#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
