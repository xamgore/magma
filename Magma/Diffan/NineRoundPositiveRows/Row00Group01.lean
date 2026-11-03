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

/-- Kernel-checkable real RFC Magma trajectories: input bit 0,
    output bits 8..15. -/
theorem cell_00_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050392a3d321c69789d44c6c3bda0654e0bbf1f8f696547cbe1ff76fc#256) ⟨k.val, by omega⟩)
      (0x227e3747#32, 0x5b41fa80#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_00_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a884d343f04e66103db19eaef9f484bf4f17b3f9d00689cbb6730600#256) ⟨k.val, by omega⟩)
      (0xc9c1055a#32, 0x77e54aa5#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_00_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cd1558918a27d5b699f2a228ffed3d844e07f83729785f29d2f38c38#256) ⟨k.val, by omega⟩)
      (0xfaff508e#32, 0x97be1ec8#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_00_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000098276b6d7d9d604e59b0322b086fd632bd48281e745d3b89e8a88d04#256) ⟨k.val, by omega⟩)
      (0x32236730#32, 0x19ce35b8#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_00_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f1beef0be09145c2f75373ef084b7796dfee5b7184946c3c9d80af80#256) ⟨k.val, by omega⟩)
      (0x140d3ef2#32, 0xdb6710a5#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_00_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005bb2e9516d9f8a68562741a16659452ecdce210d5150409f08820fc0#256) ⟨k.val, by omega⟩)
      (0xe2ed6eca#32, 0x47464bee#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_00_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b33a47098a348e6b72f3216b4df790009df89a6ca4c7a3a79295d000#256) ⟨k.val, by omega⟩)
      (0xd44f21ce#32, 0x685960cb#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_00_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b6b5a613acfb7c1bb9993c0f14b06ab30c2a8dfd776cadc63ea44000#256) ⟨k.val, by omega⟩)
      (0xcf6bb537#32, 0xca909f3a#32)
      (0x00000001#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
