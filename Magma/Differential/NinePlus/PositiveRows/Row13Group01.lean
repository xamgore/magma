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

/-- Kernel-checkable real RFC Magma trajectories: input bit 13,
    output bits 8..15. -/
theorem cell_13_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004a889f00b44d8b8212ff1084be6bfd081914c48378a0aa627b843708#256) ⟨k.val, by omega⟩)
      (0xd207ab44#32, 0x5ec3d88e#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_13_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d48c27ffd44397dc131ac08cef3b157f4b1dfc445ba8d200c60e76d0#256) ⟨k.val, by omega⟩)
      (0x05877785#32, 0x112e4c43#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_13_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000702d5fff9ced47388175348a7307a7d896c5824cd82cb775f8f480ff#256) ⟨k.val, by omega⟩)
      (0xac340c6a#32, 0x87ecbcd2#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_13_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fc65e1ba2ae032e5bb7f3c014825d6ff272ef6cb4924bce3fd54a287#256) ⟨k.val, by omega⟩)
      (0x8981cbe6#32, 0xf1ec71b0#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_13_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ab73f389afdd09248e0a9908e0495c8d2aa23fe15d3eb1c863270fd0#256) ⟨k.val, by omega⟩)
      (0x665c418c#32, 0xfd0adbea#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_13_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7e21ffffdbe1cdec4c3b6adbf0986a21fc58261336fb0cf0305107d#256) ⟨k.val, by omega⟩)
      (0x4b5fe9c7#32, 0xf11473af#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_13_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001c7f27fe1751aa3af86861cb3a8a9ae7c7728ba408a5fe6cf280b0f8#256) ⟨k.val, by omega⟩)
      (0x8ea41ace#32, 0x591e9b4a#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_13_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000009f34fffaa69ec759fd761c2789b3c96e5c5c79b8e3aee8fdb673f8f#256) ⟨k.val, by omega⟩)
      (0xe8428fc9#32, 0x11c9ffa5#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
