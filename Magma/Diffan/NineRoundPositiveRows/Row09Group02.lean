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

/-- Kernel-checkable real RFC Magma trajectories: input bit 9,
    output bits 16..23. -/
theorem cell_09_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bec568bde83a53a1576460adde3855ff09f75638d49d89e28004c003#256) ⟨k.val, by omega⟩)
      (0x7bf9d34f#32, 0xc581b309#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_09_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000062c4027f73bbb923fd8038fbebd65ddff26bdd27ef0d40948cd6f80c#256) ⟨k.val, by omega⟩)
      (0xae61ad1b#32, 0xbcd1a0a4#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_09_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fe3e32ff32d31ee6480899e2b96327e81b0babf638da1ecc3e6cb9a3#256) ⟨k.val, by omega⟩)
      (0x0d00813a#32, 0xaf20e327#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_09_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000020d13cffc9994547a426ffc36b013c1548cfee1ff7270cc673f0fff8#256) ⟨k.val, by omega⟩)
      (0x13492828#32, 0xbf051cfa#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_09_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008af1f22e24b0dd938cb9814b121c6623911f653b3b272332ad684960#256) ⟨k.val, by omega⟩)
      (0x6d60533c#32, 0x385c4176#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_09_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000005e5a1ff7a4cbc203e02fd41e7c8f0d63982da9e7c1f3ba8b951ffff#256) ⟨k.val, by omega⟩)
      (0x6ca21ea6#32, 0x7a0acae9#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_09_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000048469884c39b6259206032fe00aeaffaf65b6fe1629d1ba0c127dec3#256) ⟨k.val, by omega⟩)
      (0xe8ed0842#32, 0xecb9d61a#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_09_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7396eff8aae52440214797d4cb5a8b716f3780a53830c663fbfff80#256) ⟨k.val, by omega⟩)
      (0x1acb7115#32, 0x75af59c0#32)
      (0x00000200#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
