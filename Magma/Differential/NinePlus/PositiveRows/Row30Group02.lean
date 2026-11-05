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

/-- Kernel-checkable real RFC Magma trajectories: input bit 30,
    output bits 16..23. -/
theorem cell_30_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000038f800003ac6e5886f389c9948bf145913960485f8f24dcd52f30da0#256) ⟨k.val, by omega⟩)
      (0x2e36413a#32, 0xba83d125#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_30_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f0000000a3d89c25424c1b6ca48088b254285352b70ded23ea518080#256) ⟨k.val, by omega⟩)
      (0xb1415026#32, 0x4c4b8a49#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_30_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d000a0003019195e47fffaabb4c7f93ac6a7817c6f4d45ee1f8bf800#256) ⟨k.val, by omega⟩)
      (0x51293419#32, 0x65fbc683#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_30_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000098000000661060d486a330c6b4ba2e43cabed79ca6ac592ae0670000#256) ⟨k.val, by omega⟩)
      (0x2c979643#32, 0xba53f1d2#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_30_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0000000b9a155be59894b4c8fb7c9c3cbdd528c2da553df200f60a0#256) ⟨k.val, by omega⟩)
      (0x2edd9c89#32, 0xed43b33a#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_30_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006000e000e7e39cb7766751dae59f4e075f046cc0e1214738a8580000#256) ⟨k.val, by omega⟩)
      (0x53195ab1#32, 0x573155ee#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_30_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000040000000237c4d1a388bb328e49ad4c0b4d6766cf569e2fb40100004#256) ⟨k.val, by omega⟩)
      (0xcc9cde56#32, 0xbc7a0ee6#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_30_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090ffe00062e10ea4b3228171e662be1beff35b6d19158e556b5fe033#256) ⟨k.val, by omega⟩)
      (0xe3704d73#32, 0x8b70af0a#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
