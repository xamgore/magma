module
import all Init.Data.Range.Basic
public import Magma.Diffan.SixSevenRoundOuterPositive
public import Magma.Diffan.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 18,
    output bits 0..7. -/
theorem cell_18_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ada1ffff58ab8d57e4637dff8e44dc7d91f749e037e5a15ec7f30569#256) ⟨k.val, by omega⟩)
      (0x2d955dd1#32, 0xda816d7a#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_18_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000008d2ffff13ceb1bfd5b3489f6c5f83adbe03cb9928510af5bce79296#256) ⟨k.val, by omega⟩)
      (0x92e129cf#32, 0xfe4ffd8e#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_18_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e98c3ffb0e6c8c8d283ef14371487ffbf233c43e6a102d0de2006395#256) ⟨k.val, by omega⟩)
      (0x9827b990#32, 0xf64c3c2b#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_18_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009902ffff904201d3ee43eb98c5b4248c56765cf7aa28abda30357123#256) ⟨k.val, by omega⟩)
      (0xcfaa2aa6#32, 0x1d853bec#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_18_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004cabffffc786a9e555d9eb1cbcdb001888e64d7a5878aa7665ba3113#256) ⟨k.val, by omega⟩)
      (0x7149a5fe#32, 0x57669049#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_18_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001a62ec5c83dfde6a9404557cd8e07b184e0472f1268027627479e15c#256) ⟨k.val, by omega⟩)
      (0x438b50b3#32, 0xc96e047c#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_18_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004b4c07f8444a0cb46a22cdc34b8fa2da39f17657965704696f2450aa#256) ⟨k.val, by omega⟩)
      (0xc5c16ce7#32, 0xea5828bd#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_18_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004f9a7ffff15ce5458f6512aa068b35348aaf1dd9c5fb049ca8b9ca60#256) ⟨k.val, by omega⟩)
      (0xa9c17986#32, 0x87832e44#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
