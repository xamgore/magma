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
    output bits 16..23. -/
theorem cell_00_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cedf44cf4f66bf8ffff8e9655bb3131ec1bfd89f05297e69a794b6a0#256) ⟨k.val, by omega⟩)
      (0x3f310d74#32, 0xd0770432#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_00_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b4d6a7d3628e260b4b5e7539b0edcc551d8b7facc33ba2e78cb6f690#256) ⟨k.val, by omega⟩)
      (0xa4559910#32, 0xff77dd49#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_00_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001da0c7cf1efeb27bfb80a5492fd763e3b805f796889743031e296a5c#256) ⟨k.val, by omega⟩)
      (0x084e044c#32, 0x687ed32b#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_00_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b3822b53ca846177f86f7e5a2954f3c96545d901ab44636e446bcf8f#256) ⟨k.val, by omega⟩)
      (0x070addfc#32, 0xfd593c9f#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_00_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5ec7b513c57141b72c3a398e6ec69f89b18ac457b837dbb644fe070#256) ⟨k.val, by omega⟩)
      (0x52a6fb5a#32, 0x91a03e5e#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_00_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007bd7a2ad3c155483a565a9db0f3cd3266a106ea6e25ce8d20ddb402f#256) ⟨k.val, by omega⟩)
      (0x7b098035#32, 0xa712db36#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_00_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a084fe0146b9a9e9b384a8bc8fa618985fe3848ff71ac1608d330083#256) ⟨k.val, by omega⟩)
      (0x9ae543e5#32, 0x8ec8f179#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_00_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000029371083690dc0ed50fc3de13a378c131a2703f9362a650cb689ff81#256) ⟨k.val, by omega⟩)
      (0xeae2f701#32, 0x484ce0ad#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
