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

/-- Kernel-checkable real RFC Magma trajectories: input bit 1,
    output bits 8..15. -/
theorem cell_01_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fd2a92fa1fa51946690d5667d65f121e64bc4c04ae1d6610a809290b#256) ⟨k.val, by omega⟩)
      (0xd1aee81f#32, 0xdef3d67d#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_01_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006f5da31ae47d15044b202f2b2f4919f2a42cdc15a52734328f2b2f0f#256) ⟨k.val, by omega⟩)
      (0xd5b3a59d#32, 0xf854543e#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_01_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002026ef928648519bbf2f1bc8e39390de3d801bb1f1c19fe936cb3aff#256) ⟨k.val, by omega⟩)
      (0x48e393c6#32, 0x135c2d6c#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_01_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000061d3e10f8e08a7611d1feba5b1b72918919a9d4b1b6196dcc14af79a#256) ⟨k.val, by omega⟩)
      (0xe99a06a2#32, 0x4df7ce7d#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_01_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e5bc710185382eb5787b99db99c0bda8f2468fbd9d6b6c0bce416d00#256) ⟨k.val, by omega⟩)
      (0xb13f3a02#32, 0xc8827542#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_01_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000515fd1a198e9e3f0fde9f186f42273ebc881343946181756aff31520#256) ⟨k.val, by omega⟩)
      (0x44b961df#32, 0x9b025127#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_01_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a55dbe2e17e99533b2cc3073629e7604499e49fcd7b5b6f41c701fff#256) ⟨k.val, by omega⟩)
      (0xa31ba394#32, 0x80712030#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_01_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0af5041087650004f4322ff643b726462cb6619eeec41701b8814d4#256) ⟨k.val, by omega⟩)
      (0x7e203d43#32, 0xabf97888#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
