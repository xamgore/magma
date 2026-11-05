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

/-- Kernel-checkable real RFC Magma trajectories: input bit 0,
    output bits 24..31. -/
theorem cell_00_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005b77fa51aadc790fb21df5309bb78deb0112905a082db13406800000#256) ⟨k.val, by omega⟩)
      (0x0ea0fa62#32, 0x9580028e#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_00_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000449be821407289ddd73633d8e5fa4c6cbe363bff964fd95b44fff807#256) ⟨k.val, by omega⟩)
      (0x90bb5a92#32, 0xa5a18097#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_00_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000016f1e635c3f22c02a387844394df68c2721734f723f2dbbdec67e200#256) ⟨k.val, by omega⟩)
      (0xba5a2a9d#32, 0xbded7612#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_00_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d6a693db058f9735e212abc3f3c42d46798e751884d943c4427d8080#256) ⟨k.val, by omega⟩)
      (0xef291c3c#32, 0x4eb878e8#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_00_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000082be9a336f240349f4fd3b7e07b0d3d597da3efa733e76392fffffff#256) ⟨k.val, by omega⟩)
      (0xcfeffcbf#32, 0xf13fb2dd#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_00_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000935c67410dfc2d6c4257f2394a0ae6c161a3c6c7a310abb7f0b9ccd6#256) ⟨k.val, by omega⟩)
      (0xdcb298e8#32, 0x4d1f542c#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_00_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f962313135c2dd29bfa264ae8b0226dffe508dd92c928d0149f10f80#256) ⟨k.val, by omega⟩)
      (0xd37e597d#32, 0x94cf3cb3#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_00_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f0c47787e4d2ae5a1e8159ce8744eaa0fbdfdb7579410d2b2347a025#256) ⟨k.val, by omega⟩)
      (0x775d8243#32, 0x8f93dc7f#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
