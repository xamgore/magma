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

/-- Kernel-checkable real RFC Magma trajectories: input bit 27,
    output bits 8..15. -/
theorem cell_27_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003bffffff532a3b11092e0eeae371ab1e85d9aebf6577f75aee3a32ff#256) ⟨k.val, by omega⟩)
      (0x533a50b1#32, 0x5a7f7e73#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_27_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000017f30bd6622ca9e9bb7690d1f1398e9dff5b23ae052bfe6d0bf87d00#256) ⟨k.val, by omega⟩)
      (0x7016004c#32, 0xa44faad0#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_27_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008531ff0fe5b689e7320e4064b7f26d28397472621e7725dc39225560#256) ⟨k.val, by omega⟩)
      (0x5709cfa1#32, 0xb58ecc77#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_27_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000066c00ffef60c1d3d7193e40064c00fcc5b46f45ff738f63aadef85c7#256) ⟨k.val, by omega⟩)
      (0x4a3a83bd#32, 0x7b4a2c55#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_27_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000038ffffff9f3d498ca099075c6da03bfd37726495b670e1749c68cfc0#256) ⟨k.val, by omega⟩)
      (0x395059bf#32, 0xb2988b26#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_27_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7000000d210f1d47532029eaadb7252d278904952db14cd6867f000#256) ⟨k.val, by omega⟩)
      (0x331de829#32, 0x48323915#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_27_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e55fff8d676745d7f01f5be229c8eb1f28af7ef6d7cd4837d3275200#256) ⟨k.val, by omega⟩)
      (0xce9d520e#32, 0xf8a73237#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_27_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5f800c265d0c2635dc84c43e00f5713f03b8cecbfb9105603a04315#256) ⟨k.val, by omega⟩)
      (0xe0f3a901#32, 0x183cbebe#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
