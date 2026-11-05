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

/-- Kernel-checkable real RFC Magma trajectories: input bit 7,
    output bits 0..7. -/
theorem cell_07_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008b712fbf44be3e6d605760d10fdb14528a0d0fc4bc8b19aad0359ac7#256) ⟨k.val, by omega⟩)
      (0x137b1ae1#32, 0x874038c7#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_07_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000029483a3fb34850862cd33f012fe94c93ee715ab61b6b51600ed9a351#256) ⟨k.val, by omega⟩)
      (0xa49a1730#32, 0x504492c4#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_07_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000093f5dc89f081c8f3213f05841bac9b0a7a137ab183605793a925aa3b#256) ⟨k.val, by omega⟩)
      (0xea5652ce#32, 0x72bf7018#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_07_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007b8d13c7ac5c2d0c3367b17395759a35050083446194bf821e553a69#256) ⟨k.val, by omega⟩)
      (0x91d74972#32, 0xe13ebbc1#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_07_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000055afab3d885edf82c6fb483c2074592b41f48c33134607032c4e4696#256) ⟨k.val, by omega⟩)
      (0x2f19db81#32, 0x28fbad3f#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_07_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d3dc0d6f99b7a7df0773eeca68016b4798038c171238b8fbaefcf0ef#256) ⟨k.val, by omega⟩)
      (0x74f3a628#32, 0xcf425ce4#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_07_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ab97a91257fffd554b83663f5d437f0e7f531f9ba9114177b8e099f#256) ⟨k.val, by omega⟩)
      (0x90d4f590#32, 0x05c044a8#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_07_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003bdab77fae1c5eb5780ae58d1ca55655017c7d4fd552010496fef7bc#256) ⟨k.val, by omega⟩)
      (0x781f61fd#32, 0xfe885aa5#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
