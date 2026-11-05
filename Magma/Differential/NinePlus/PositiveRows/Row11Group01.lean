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

/-- Kernel-checkable real RFC Magma trajectories: input bit 11,
    output bits 8..15. -/
theorem cell_11_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000055298c7ce73e54cff992119f44a210c7c852028cee1ade37fa429f00#256) ⟨k.val, by omega⟩)
      (0x4e731d91#32, 0x2b104b5a#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_11_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001f49f6ff7840d97fb0523ead6b9322fbe05d1a646f7337e52f235acf#256) ⟨k.val, by omega⟩)
      (0xdb6b1a2e#32, 0xbb4db05d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_11_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d6429bff8a993ca65b66b39e69e805ed69d8f96d0f40a0fa8290a507#256) ⟨k.val, by omega⟩)
      (0xc9fec22d#32, 0xf64c53b1#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_11_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003a7619fff11e6e750ac2c7cbe25b2cde5ee05d21a6b418b4549d6b0f#256) ⟨k.val, by omega⟩)
      (0x648e4bed#32, 0xf75f2ff5#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_11_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f8212afe84403e610dafc17678112bddb885255a3987bca0751c87b0#256) ⟨k.val, by omega⟩)
      (0xdf025747#32, 0xd929b94f#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_11_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c6e89a5d8d000f9067f1854371864c3005333f93c10a6ab68da05f30#256) ⟨k.val, by omega⟩)
      (0x3ae73978#32, 0x6e0338e6#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_11_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003bf4dcc04c45657de5986d17c9e8f64e69a025efa24ab5c1964ba3e0#256) ⟨k.val, by omega⟩)
      (0x7baa1237#32, 0x4a126b2b#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_11_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005068f7fcaf340c1604efc734007260216c17194e9e2dad839dd1a203#256) ⟨k.val, by omega⟩)
      (0x7f261be4#32, 0x1c6d3e2d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
