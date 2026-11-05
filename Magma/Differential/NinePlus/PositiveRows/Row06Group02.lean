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

/-- Kernel-checkable real RFC Magma trajectories: input bit 6,
    output bits 16..23. -/
theorem cell_06_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000eb9dd32feafa7ac0ee36d524bf7f5f8d3f063e180dd86d176ae09ffe#256) ⟨k.val, by omega⟩)
      (0xd5bd3aa1#32, 0xdf9a8093#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_06_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dd0934409922d94c03a340b5c59c51b1b743a865470fa0a76d5e0000#256) ⟨k.val, by omega⟩)
      (0x2ee94340#32, 0x0fef4dff#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_06_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ce1d502fcd69b7f9f50f7a9fe9cdee3711ed46f05651c582642bffff#256) ⟨k.val, by omega⟩)
      (0xdd2417fb#32, 0x40ee2fdb#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_06_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009ff5b117bc3ab6214fd9f1fff3dbaaf17ed2eb16814be102302c4865#256) ⟨k.val, by omega⟩)
      (0xafc64929#32, 0x90f76d1c#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_06_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b95c82d0b5caf56215c5e3b1ab4520e8d0c427deff0b8d984ceefac0#256) ⟨k.val, by omega⟩)
      (0x017ac25f#32, 0x21b8603b#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_06_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000705249d0432daa94027fc4f1922d7c31d95e4dd479604eabe1900000#256) ⟨k.val, by omega⟩)
      (0x7e333a3e#32, 0x623a1c15#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_06_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009160112fefb49ff86b04d9f8450fe306e08b0de911eabd2ec19ff80f#256) ⟨k.val, by omega⟩)
      (0x5b9945e3#32, 0xb29edfd5#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_06_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000afcc834e896267ef8c036a3001cac93e0816a57e3985edd8707fb410#256) ⟨k.val, by omega⟩)
      (0x5fb9fc06#32, 0x09ae696c#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
