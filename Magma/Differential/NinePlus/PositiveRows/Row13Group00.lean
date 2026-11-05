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

/-- Kernel-checkable real RFC Magma trajectories: input bit 13,
    output bits 0..7. -/
theorem cell_13_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000081cb000eadf0afeae43323337247662fa41b77d9b7bfe28e8af927b#256) ⟨k.val, by omega⟩)
      (0x381fbb0a#32, 0x20e96546#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_13_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ce5330056bc393e56d014bac23f684b461873aa0707cc3e1c123d04e#256) ⟨k.val, by omega⟩)
      (0xb40ed306#32, 0xc1085cab#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_13_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f95bd0000af8be8e83168d0dc470d7945812b62c94ea678bc7a826b9#256) ⟨k.val, by omega⟩)
      (0x6bfb44b2#32, 0x9a693998#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_13_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a464dfff6984ceab9cbcff37e4b50d1c955888ae90c40ad2d61be287#256) ⟨k.val, by omega⟩)
      (0x593c2e13#32, 0x1b47cf9b#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_13_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bf61a0ff9b4769955b33e23c86d6c3383b391e88cf495ecf3b71b310#256) ⟨k.val, by omega⟩)
      (0x6b5a1652#32, 0x0cccc61e#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_13_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ba6a5b6c8c11c2dc6562cbdcbc4c122d4225f8ae7243a5eab7a42ea0#256) ⟨k.val, by omega⟩)
      (0xb1916b6f#32, 0x784b9f49#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_13_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000717561ff0e0579de2c24251784e6f4015dc65adf2044c18476529a50#256) ⟨k.val, by omega⟩)
      (0x7b84f9dc#32, 0xaa66b578#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_13_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008f9a0cd427b1ea4218e94597156266293300f4f859e2be2fa6499245#256) ⟨k.val, by omega⟩)
      (0x06f2b0d6#32, 0x218e4499#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
