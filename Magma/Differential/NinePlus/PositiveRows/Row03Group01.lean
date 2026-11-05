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

/-- Kernel-checkable real RFC Magma trajectories: input bit 3,
    output bits 8..15. -/
theorem cell_03_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000041471193581767cea4f54a557aab8bb10f52cd144f882dfc0a986c0#256) ⟨k.val, by omega⟩)
      (0x77bec3f6#32, 0xaeeb6857#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_03_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005d8081aa3846e07a63fb361bbd9e74946f1d59c0a3eff268f779de47#256) ⟨k.val, by omega⟩)
      (0xc10d7871#32, 0xd33a28ac#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_03_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a0a8eda4e8bab3fa0170b22f8fd2f63489e9effc6ca1a39acb2fc4f0#256) ⟨k.val, by omega⟩)
      (0x394b899a#32, 0x15400477#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_03_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fb1572e59e7dfc07b17fceceaf2990930cb4918edc70adef915a5400#256) ⟨k.val, by omega⟩)
      (0xfbcdb7c4#32, 0x5a093c1b#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_03_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000010a574f9c46265e54b18ffab84620fe590d6087833c079727270c9cc#256) ⟨k.val, by omega⟩)
      (0x602e9360#32, 0x4c12741d#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_03_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005bae79c66f8c852d7485601e598d0c0c57c233b2ad4f7f77d97dcfff#256) ⟨k.val, by omega⟩)
      (0xe5ff5b60#32, 0xad63c2d6#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_03_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dee96cb24c658a81a4a9d87071c8fb45b26d09b8a41c2ad00e3e2b00#256) ⟨k.val, by omega⟩)
      (0x92975905#32, 0x809e8f37#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_03_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000058f405ea185e2c7807f0fdddcf0c3dfb807b2187b6b7e9622aea80cc#256) ⟨k.val, by omega⟩)
      (0xbe094f46#32, 0xad272f62#32)
      (0x00000008#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
