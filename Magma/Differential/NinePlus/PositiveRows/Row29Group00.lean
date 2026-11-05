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

/-- Kernel-checkable real RFC Magma trajectories: input bit 29,
    output bits 0..7. -/
theorem cell_29_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000010010000afb662895493fb2e41d7dac4c9f49c9edf4189c2d1427c27#256) ⟨k.val, by omega⟩)
      (0x67d8f08e#32, 0x40146a00#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_29_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000060ffffff5331b48b510471cfbbf93f978c1744fa64cf534e008acd3a#256) ⟨k.val, by omega⟩)
      (0xdb1eac04#32, 0xfb056569#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_29_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000078038000925c369f0926cc9bd54842c0f69396b6761a618aeb9e7f5e#256) ⟨k.val, by omega⟩)
      (0x08ca2583#32, 0x3d66e7d3#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_29_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000040002000470fe51e334b928727ff9788074079753d36e5caa19c41aa#256) ⟨k.val, by omega⟩)
      (0xf25c48be#32, 0x41059f80#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_29_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000600020008cee351862381df13e3123008fb5e47d3a775fe17304bf30#256) ⟨k.val, by omega⟩)
      (0x5d145971#32, 0xe706dfd5#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_29_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000765897ffc5010506e32ffce83103604baa96ea2767cdc4efbde27413#256) ⟨k.val, by omega⟩)
      (0x479554f8#32, 0xf4b3325b#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_29_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000000e6179cb857f5c84d13ca9d6fbbecac36f908ecfd867752e60b232#256) ⟨k.val, by omega⟩)
      (0x698b997a#32, 0xe9cfa0ec#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_29_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f800f00052e0b4ffc79a7ecea693d4e5a7fa51b94e567b8b1f50a990#256) ⟨k.val, by omega⟩)
      (0x5af8a038#32, 0xa853e8db#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
