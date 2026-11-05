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

/-- Kernel-checkable real RFC Magma trajectories: input bit 4,
    output bits 16..23. -/
theorem cell_04_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000baa5d9162016d2f8302d360d5e23128a2984a9cceaabf4cd89c94bf2#256) ⟨k.val, by omega⟩)
      (0x155057d6#32, 0xf4461aa8#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_04_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c23598f84dc12eeb86df9f6edf8e8292001a1729e72eef5b2cd9f80#256) ⟨k.val, by omega⟩)
      (0x86eafc9c#32, 0x517fae76#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_04_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000018344c3782105833b23fa5d2d5f7331da434196a49bc7ce34523ffc0#256) ⟨k.val, by omega⟩)
      (0x8008b0ec#32, 0xbfed630c#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_04_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d3d093c2236650d315533e68bb5c3d6a62dc6564d5ec82a858a8c3f0#256) ⟨k.val, by omega⟩)
      (0xb3dfb502#32, 0xb8203cd4#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_04_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001ba84cf3ca656e3160b3fe12408b9e82128e7bc3ecb2c4efc4cef8c0#256) ⟨k.val, by omega⟩)
      (0x05b55fff#32, 0xccc18c6a#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_04_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000015deba97a714e9fd12a9a38e0a5177e0b502ec978006a4bd53586f50#256) ⟨k.val, by omega⟩)
      (0x41578e6b#32, 0xbead0fd7#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_04_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000037c17f88d2cb7c1f84eeb7df5317ae7537e1c18a8475eb7e1e2bd100#256) ⟨k.val, by omega⟩)
      (0x9596000d#32, 0x41ceb28c#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_04_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090c7979fee0bfa051a1f049b67e6918dc3cb3d3f0f4b86091780fc0d#256) ⟨k.val, by omega⟩)
      (0x5297f3f9#32, 0x1659f5fd#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
