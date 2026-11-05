module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 3,
    output bits 0..7. -/
theorem cell_03_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a26ab7e37e94b8587b7835f93df9e54f2878d5ae05db03fa810478ff#256) ⟨k.val, by omega⟩)
      (0xc40ad959#32, 0xf527c1f3#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_03_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000022dd4c941fb0d904c5c5166d8f5d84ae3d8a773f19902e5bb1701362#256) ⟨k.val, by omega⟩)
      (0x68fb9446#32, 0x295bf021#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_03_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000568819d6b31b9e6ef57794800a3db45ba7654d52bce7cfdee0460cfa#256) ⟨k.val, by omega⟩)
      (0x92864fb8#32, 0x72497c35#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_03_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004bade6826a313c6ba269f176a434fdc1286b8344d79251e681a8db8c#256) ⟨k.val, by omega⟩)
      (0x50e7c543#32, 0x6f73bec6#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_03_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d28964a8ce4e23140a2e72f07f365e6f9bdc4536b9d9aa4030648b50#256) ⟨k.val, by omega⟩)
      (0x5f25d58f#32, 0x3d772c07#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_03_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009f0c24130bb42122af400d042e45231eb26d5407683555cc63a8a260#256) ⟨k.val, by omega⟩)
      (0x8bb279f0#32, 0x8228e331#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_03_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c1ae1a5a1d8b4cb49269bd5ba68d1cb31709a89dbc72e6d68ee5734e#256) ⟨k.val, by omega⟩)
      (0x36a67a36#32, 0x9e8538fd#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_03_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000057bef8fac40287bad7fe103f6b9c63db0d1ea5e0cb744793687b47c0#256) ⟨k.val, by omega⟩)
      (0xbb4d7de0#32, 0x5c5aba1e#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
