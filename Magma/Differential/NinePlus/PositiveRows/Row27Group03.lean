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
    output bits 24..31. -/
theorem cell_27_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000970000000c5f1a619bd8b1a889da8ca55fa3ea4153e79c039ac06030#256) ⟨k.val, by omega⟩)
      (0x571af11e#32, 0xbd9c7afe#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_27_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000087c000008f4c12a3dc8501a7e90c19fedf8b03ac7c28332de5f80000#256) ⟨k.val, by omega⟩)
      (0x2785c90f#32, 0x1909f79c#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_27_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fa00000035e423e989069dfe1731b49d51a8ede7b514494949007c00#256) ⟨k.val, by omega⟩)
      (0xd106920b#32, 0x1f903cea#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_27_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000051000000d167943e985303f8501cc351461f4b1fe3826dd813e00000#256) ⟨k.val, by omega⟩)
      (0x6dd067f3#32, 0x31535cb4#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_27_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000029fc0000f09babf5cc4e062b71915dfcee5efe599c3ac97ef57b0b00#256) ⟨k.val, by omega⟩)
      (0x5bc83ea1#32, 0x5536bdfc#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_27_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000058900000f05c2d51efeeb491064371ce1d049210d09435f45c0b000d#256) ⟨k.val, by omega⟩)
      (0xee8d7e59#32, 0x196c58a2#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_27_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004d3800008e068cad40bdd048e894d4f670838448d1f6c0d1d024008c#256) ⟨k.val, by omega⟩)
      (0x55af0139#32, 0xd6f8d446#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_27_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f90be04004d0eaca6bee23c214a3846f3e7fe682606a83f0882aa6a6#256) ⟨k.val, by omega⟩)
      (0xf5ad8cbd#32, 0x7554c2ae#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
