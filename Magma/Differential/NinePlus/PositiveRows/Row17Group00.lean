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
    output bits 0..7. -/
theorem cell_17_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000051db7dfaed7df51e323132d78def1d798ae7ab4864c9a1abe240a963#256) ⟨k.val, by omega⟩)
      (0xa9bf0ca6#32, 0x9e336125#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_17_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f954fffebdac30be6814ede8bdfa6e68a84b332ee0e03c9df161175e#256) ⟨k.val, by omega⟩)
      (0x548902fd#32, 0x5abadba4#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_17_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000032f9f3c15db30d9b42c98fd371a2be8be4c3635d1aaeadca7c762719#256) ⟨k.val, by omega⟩)
      (0x79ab1688#32, 0xc71dfadd#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_17_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006ff685ffefab4b0042b45719667194f13f632bb83c252685f488dada#256) ⟨k.val, by omega⟩)
      (0xebc9366e#32, 0x768c8306#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_17_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000081eae3ff865f7c1c887e5bb6fb04e445d94ff0ec9f8a83f3a9fb11f0#256) ⟨k.val, by omega⟩)
      (0x58a0abd2#32, 0x977b6c42#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_17_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000029ed3fffc2aeaf075459402055b60da87dbb7eb97fa7423c261cfeaf#256) ⟨k.val, by omega⟩)
      (0x6d623fc7#32, 0x1825783d#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_17_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000abe25e218081382feb3c81562dc5d5a560a2f545b73971c0461fb040#256) ⟨k.val, by omega⟩)
      (0x6d477bdc#32, 0xf0982036#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_17_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e79cffffa7122aa46538389d8411d14f8fe7a060804adefd9c3ef94f#256) ⟨k.val, by omega⟩)
      (0x8b5cfcd8#32, 0x29f7da98#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
