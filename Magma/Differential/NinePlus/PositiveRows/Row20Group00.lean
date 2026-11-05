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

/-- Kernel-checkable real RFC Magma trajectories: input bit 20,
    output bits 0..7. -/
theorem cell_20_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dff00000bb47ed7245a6a7ebd71d81b0388624e54489298d617c4ba9#256) ⟨k.val, by omega⟩)
      (0x4d31482b#32, 0xca345e15#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_20_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000007f37ff9ed361ef9cd703b85cc87dfd33172816749b754f272f7845b#256) ⟨k.val, by omega⟩)
      (0x9d1524f6#32, 0x6fffa92b#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_20_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004f0fffff45f68b0ee3f68b15737b02d1708d4790fe9eea690feca7f3#256) ⟨k.val, by omega⟩)
      (0x3059ae09#32, 0x17143bd8#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_20_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000abd7ffff415c4fc1f09cc35a8649a8e170f9440475da4a3ee3d89396#256) ⟨k.val, by omega⟩)
      (0xbe0349cd#32, 0xd34bd10f#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_20_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e1370796a531440665e330a345ad15bddf38b4bc4fafb21b1815b1d0#256) ⟨k.val, by omega⟩)
      (0x55923460#32, 0xf6dc7369#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_20_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008e6c3ffe4a3bb5cb6d5e77a008609d9f9bd69a44ebf53ef59c0d8bb0#256) ⟨k.val, by omega⟩)
      (0xb76767f2#32, 0x384f4c66#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_20_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000039b44efb43fa5abcadbcf3b091cadb534d5c05d2344ee4276b47ed50#256) ⟨k.val, by omega⟩)
      (0x90f006f1#32, 0x98734b22#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_20_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a6dc0000769f7981cd89bcc8e1f44fcba3a8557d5d918e8065486040#256) ⟨k.val, by omega⟩)
      (0x89ed9410#32, 0x55363a3c#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
