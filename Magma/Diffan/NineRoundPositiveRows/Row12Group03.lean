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

/-- Kernel-checkable real RFC Magma trajectories: input bit 12,
    output bits 24..31. -/
theorem cell_12_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c9e8affe19d0df0c90826eec9d8b953fc005f7cfc9d2557d91093f92#256) ⟨k.val, by omega⟩)
      (0xd23aac8d#32, 0xfb2fd1ca#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_12_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000095ef2a99f3cf5c4785d1b703efb7a621055220806d151d8e74c8ffe0#256) ⟨k.val, by omega⟩)
      (0x124d7d6e#32, 0xb6f991cb#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_12_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000da7700062f488af3a013f7d02fe07fd0a376452364b11b736000000#256) ⟨k.val, by omega⟩)
      (0xe76cb2cc#32, 0x90c50e15#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_12_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c05ddd1ce975815bfe0729de40a2d6bc5f7d7a785a041c2ff6f8c0d0#256) ⟨k.val, by omega⟩)
      (0xf3080a1a#32, 0x577090a5#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_12_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000a87afffaf1156828ba7f82789fb582c69dfb0a263dc66c8309035b0#256) ⟨k.val, by omega⟩)
      (0x116bdb16#32, 0x06d4d4bf#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_12_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cbebcc009f0516e182006b0af6aa5bd5dc7df029051198a6c0043800#256) ⟨k.val, by omega⟩)
      (0x46d7bbed#32, 0x2c627fbf#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_12_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000985748008f16c11c45c7972af9df573f2d0b5ff83d69220040083000#256) ⟨k.val, by omega⟩)
      (0xffcb35cc#32, 0x56f5acbf#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_12_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c06e33ff52fa5dff9ba3fb4bec003d355a3811c08cae334867aa7afe#256) ⟨k.val, by omega⟩)
      (0x673aacb1#32, 0x6b593200#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
