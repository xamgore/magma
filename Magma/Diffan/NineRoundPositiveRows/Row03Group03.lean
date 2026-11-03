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

/-- Kernel-checkable real RFC Magma trajectories: input bit 3,
    output bits 24..31. -/
theorem cell_03_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000096b50b68d056c22f88c00127cc86ac05cb7d2e960cdb6cb280c18000#256) ⟨k.val, by omega⟩)
      (0x4d23382d#32, 0xcf245737#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_03_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a540206d031b5630dd8772f520226e414a06150494f59107ee100008#256) ⟨k.val, by omega⟩)
      (0xb869582d#32, 0x944546dc#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_03_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007eb9b5b76d52543c999d6351628975fd913cc3c4b9b9d3eb939b6e80#256) ⟨k.val, by omega⟩)
      (0x70e0cedb#32, 0xc2746bdc#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_03_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005ecdbd6b3e23a2ee7ccf8353edc1849db564234861138f2819ffffa9#256) ⟨k.val, by omega⟩)
      (0x3a9cc372#32, 0x770015dc#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_03_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000776031c500e52253ea4dc32e94655961c52298ea7089cd34b87ffff8#256) ⟨k.val, by omega⟩)
      (0x38ad9111#32, 0x23657ea6#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_03_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fcee030ae267ae4d41009843a0b32db98f3810330cb1cd46600cce1c#256) ⟨k.val, by omega⟩)
      (0x783075b4#32, 0xf0681b3f#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_03_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008619362ae8b8b5ee2c67c75f4a916a6983810ed2452cb5fe802218fc#256) ⟨k.val, by omega⟩)
      (0x1df2e76b#32, 0x34eb1415#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_03_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003c43d9d88122eeb7dd8034e51effb0028b238c5d85ae9ccf9a619f62#256) ⟨k.val, by omega⟩)
      (0xd0dff5c6#32, 0x1c567cb4#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
