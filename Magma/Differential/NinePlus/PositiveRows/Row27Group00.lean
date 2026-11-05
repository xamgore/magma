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
    output bits 0..7. -/
theorem cell_27_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000049f5d868c26ef12a335557c49f0cb8fa710f4f1b254fef95f6daafcb#256) ⟨k.val, by omega⟩)
      (0xeb492ec1#32, 0xfd1e8459#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_27_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000006f0effc5345ad272d432cf9a20bc309fa0c5286bf822b4d0a0a91ab#256) ⟨k.val, by omega⟩)
      (0xd0ae47e8#32, 0x763f5ed0#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_27_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a700000000451a3b7481a48983d4aeeab33afac90fcce32ecc5b754b#256) ⟨k.val, by omega⟩)
      (0x812d49d3#32, 0x8d7a39ff#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_27_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d96fba20d8bb08e1d691d1ab0d51ba2f8dfc49af569e8bee1eea1ab7#256) ⟨k.val, by omega⟩)
      (0x72935674#32, 0x13c30e23#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_27_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000356cc3ff420d99d9bb0e8ed34a3cd3ed19459fa4248169445bc84cf0#256) ⟨k.val, by omega⟩)
      (0x72ecccd5#32, 0x25752cb2#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_27_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000963984a961441428c8a0243437892a06c2e098401dc43d446873de5f#256) ⟨k.val, by omega⟩)
      (0x7e4136fd#32, 0xe33c61e7#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_27_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d9007d800db85c1a0a05c0bd04109b038178cf9e0341115facb3314b#256) ⟨k.val, by omega⟩)
      (0xbbed565b#32, 0xedaca994#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_27_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e959b83e228aa93ba2b03edc8248b5cd417d2d60530b7d452d8179db#256) ⟨k.val, by omega⟩)
      (0xa4a05f6b#32, 0x039aa9c4#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
