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

/-- Kernel-checkable real RFC Magma trajectories: input bit 24,
    output bits 8..15. -/
theorem cell_24_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004cf721e37e6b04a610f8bac6f0341755ff5ff825563734c0008d6efb#256) ⟨k.val, by omega⟩)
      (0x973e7cce#32, 0x7c7fa4f5#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_24_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050ffffffac6a91fba6fff40dbcea26c685f8564714284fff4a4d55ff#256) ⟨k.val, by omega⟩)
      (0xdfd87899#32, 0x9f1436e2#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_24_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005edb9113198402ea84849593b0825fb08bd852451956b17b015a09c2#256) ⟨k.val, by omega⟩)
      (0x8b074097#32, 0xd81c7b67#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_24_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f1000000f14b8b899b9e8cbbea3ccba2ca3c7c0002e71083ceaafb00#256) ⟨k.val, by omega⟩)
      (0xc2308793#32, 0x7365ed92#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_24_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000046ff80ff130443a1257dbf7ef743b07f2673fe9a6d8f05bea8ec17ff#256) ⟨k.val, by omega⟩)
      (0x134ff99f#32, 0x443185a9#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_24_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003561fffea9008c98c019027f205e81444508a5a2e63d852f3eb31540#256) ⟨k.val, by omega⟩)
      (0xd8b04c36#32, 0x64a4155d#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_24_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001ac8000030064c0c930fbf928f7fb66dbb37d00c0b4940e5777b3801#256) ⟨k.val, by omega⟩)
      (0x123a8d00#32, 0x58960fff#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_24_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000039ffffff9f2abd6da3b26f44d001ea62aff9422ae1c04c87b48b86ff#256) ⟨k.val, by omega⟩)
      (0x3efc2b6d#32, 0xb959ffdb#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
