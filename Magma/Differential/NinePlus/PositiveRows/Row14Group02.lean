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

/-- Kernel-checkable real RFC Magma trajectories: input bit 14,
    output bits 16..23. -/
theorem cell_14_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000020f9fff228921c80b8a4d1a3c462514640ff90c09c457b89d98efc0#256) ⟨k.val, by omega⟩)
      (0x6392f40e#32, 0xb34c0c67#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_14_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000023a45762701306a4980a202033a6244880d7e2e1a4729ec8db7d0085#256) ⟨k.val, by omega⟩)
      (0x50e0bbae#32, 0xb4ae8a00#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_14_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001531dfff6fcf9a32e891dc401b4d187ff20de7df96d7d132ce8afff3#256) ⟨k.val, by omega⟩)
      (0x3c29400c#32, 0x4e344c99#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_14_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000891eb3ee12c5e3e480dd7b4818bedd4b03221c9bd35d824490a3fd3b#256) ⟨k.val, by omega⟩)
      (0x95763fec#32, 0xb84b8492#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_14_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000002896000e4168ba33abab7cca0a7be51069186d151e0fc0333908000#256) ⟨k.val, by omega⟩)
      (0xbfe9ecf6#32, 0xf493b19a#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_14_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000509de0a67a5fc00bbce9fd50a660f6091902a72cbe49fb86ff473ccd#256) ⟨k.val, by omega⟩)
      (0xd707803c#32, 0x277fd6c6#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_14_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ee2a380014e6f48c34e5f6b7666b61a03f96cbd6ba3bf41541400000#256) ⟨k.val, by omega⟩)
      (0x3233b177#32, 0x821b8c76#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_14_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000047d83fffb6ea3747a47a228d4e7ada0b66aba7fa801b2132d75d301f#256) ⟨k.val, by omega⟩)
      (0x8226d87c#32, 0x8c89af2e#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
