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

/-- Kernel-checkable real RFC Magma trajectories: input bit 16,
    output bits 0..7. -/
theorem cell_16_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002d94ff7c985e844563d981dc9506fae72c91ae8f5b305788f0e100e5#256) ⟨k.val, by omega⟩)
      (0xed6f89dd#32, 0xc767df19#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_16_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a122ffff0af04a678e46bbade1615320cca65089e54d03db407a40c2#256) ⟨k.val, by omega⟩)
      (0xbf32c3bd#32, 0x304bc7d3#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_16_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000109afeffe1dd6c5c24b054adb97c7244072bab4bbc6963087380371d#256) ⟨k.val, by omega⟩)
      (0x7ab2f6ce#32, 0xecedf6f8#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_16_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000cc32ffeccc0c43a4bb79922c26128f9d98911ec2fba13de43149939#256) ⟨k.val, by omega⟩)
      (0x8bdc13d5#32, 0x8d2a3ce4#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_16_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000613091f80c8f2ab8731d48016e01a5b5744c3323fb37b4090d863572#256) ⟨k.val, by omega⟩)
      (0x6442e83c#32, 0xb03fe95b#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_16_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008b1525fd33d4943430ae9bb2a381ffb754384601114c501fbad39cb3#256) ⟨k.val, by omega⟩)
      (0x8df18719#32, 0x449221a7#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_16_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ee2f1fff2ad904eacded5484085eb579ca74ba28b120ed1937b8763f#256) ⟨k.val, by omega⟩)
      (0x20ff7b28#32, 0x001b22f5#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_16_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a406ff7f39ed8f49f4e556432143043bafbc59e5222335944ac3d039#256) ⟨k.val, by omega⟩)
      (0x14bad6be#32, 0xefaad364#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
