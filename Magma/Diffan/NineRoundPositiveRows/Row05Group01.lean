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

/-- Kernel-checkable real RFC Magma trajectories: input bit 5,
    output bits 8..15. -/
theorem cell_05_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a64ba78f4acbc42d99154ef31c9951300ae453a0091837ef000caae3#256) ⟨k.val, by omega⟩)
      (0xbd1dde66#32, 0xdebde23c#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_05_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002344bf1f36e7b6c9a84c60a96ac1f88a70ba1dffe4fca36b35bd358e#256) ⟨k.val, by omega⟩)
      (0xb40dac01#32, 0xc7823eda#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_05_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000034e22aa3f35192f23695bcbf8168396d9cccccaf31f90bc9721eed00#256) ⟨k.val, by omega⟩)
      (0x24f2aeb0#32, 0x15aaf79e#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_05_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000095629fa3229b80a59603dfa7e839daa004e62d0f5064bfe2ddb45850#256) ⟨k.val, by omega⟩)
      (0x421c2376#32, 0xb6ca0e29#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_05_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000068dac6744edd1980f2264f832faf01a74f286a6f05e523cac3c29003#256) ⟨k.val, by omega⟩)
      (0x04243e44#32, 0x95e47f2c#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_05_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009e2a156ae6abe5bae1441cb948908f0da5ab974c19c2caef1069e008#256) ⟨k.val, by omega⟩)
      (0xedbd5c1a#32, 0x3ea10782#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_05_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000018133acfca9e632356ce2584b0482ba6b91ba2d5adc4314a2bd2a006#256) ⟨k.val, by omega⟩)
      (0x482c7e63#32, 0xba2a638b#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_05_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002f735627d3f67375825dc96c1913ef5df10b8cec8bfaead688766fff#256) ⟨k.val, by omega⟩)
      (0x0370b507#32, 0xc74b851d#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
