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

/-- Kernel-checkable real RFC Magma trajectories: input bit 18,
    output bits 24..31. -/
theorem cell_18_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000070b70010af3171e833e7628ac0769552dae9663d0692548a44e80000#256) ⟨k.val, by omega⟩)
      (0xfbde4ab0#32, 0x8c3eb4ac#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_18_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000003e20000b41e0cafa29fcd390fd88ee72544da44c17fcb3599000000#256) ⟨k.val, by omega⟩)
      (0x4ced47f7#32, 0x3fc368d9#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_18_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ea2bfffe7bcd3e120969fcb9d253f3512efd0fef93eef3d7ab3e2200#256) ⟨k.val, by omega⟩)
      (0x8d71009a#32, 0x3c003b5f#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_18_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000976b80002fb2d658a6ca43bef7975f6b6583ced837678ef219000000#256) ⟨k.val, by omega⟩)
      (0x74d54d83#32, 0x6cf5134f#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_18_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004923300087f4236943b07da064e3b4827e6eb06d64bfe248f00b0088#256) ⟨k.val, by omega⟩)
      (0xa742c237#32, 0xeac3c111#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_18_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003a63c000b1ec55c90ced11a368491c470edf7c32c1a69c7170001003#256) ⟨k.val, by omega⟩)
      (0xe39032e2#32, 0xf1681d24#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_18_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d93d00001a05394e43ab470f9fce6c9547fd94758176cbf230003000#256) ⟨k.val, by omega⟩)
      (0x72c1635e#32, 0xf5285f23#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_18_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000455b0000e421848c94e970ed74f0d4854f351085e029cac8a2efbb8d#256) ⟨k.val, by omega⟩)
      (0x894513c1#32, 0xa6db8ce5#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
