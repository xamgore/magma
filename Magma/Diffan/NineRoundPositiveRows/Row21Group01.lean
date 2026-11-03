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

/-- Kernel-checkable real RFC Magma trajectories: input bit 21,
    output bits 8..15. -/
theorem cell_21_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a2efffeffdf4cea8cefb742421c0483c50423ddf74fad02e73d2c8c#256) ⟨k.val, by omega⟩)
      (0x1862bf95#32, 0xc185ff80#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_21_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cf10ffff6e7ca7ef28f713f4c3d8999a523e53c37eb2d5895c487f0d#256) ⟨k.val, by omega⟩)
      (0x1168c3be#32, 0x00b54411#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_21_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ad00000026e1990e04e886b35b1bd24f69384a7469e3d09c9f4e100#256) ⟨k.val, by omega⟩)
      (0x256bfa0c#32, 0x97fe965b#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_21_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000d9fffff62df55e001f047f7237df8b3f67a951ead1405db00430700#256) ⟨k.val, by omega⟩)
      (0x7e3833e5#32, 0x0a5110fb#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_21_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000025e3ffff0d3023eafbf94113e9fe9df7fa3361b0fb3b3afa2ee6b404#256) ⟨k.val, by omega⟩)
      (0x78199edc#32, 0xaddf5f64#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_21_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004952278055b5beee362b18098a788cfc5640d2e79ef9cdd3e860b41f#256) ⟨k.val, by omega⟩)
      (0x22497d4f#32, 0xc9d8bcd1#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_21_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a29fffff72db0571d59e6bfba2400a77bc59e7fbd77a84048544dfcf#256) ⟨k.val, by omega⟩)
      (0xd39f9f01#32, 0x87094da5#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_21_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004daf80ffe8e524d05f6e0e989e7cc98f075fde99e98e1a0f9b757fe0#256) ⟨k.val, by omega⟩)
      (0x1aafb68a#32, 0x25373d57#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
