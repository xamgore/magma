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

/-- Kernel-checkable real RFC Magma trajectories: input bit 23,
    output bits 0..7. -/
theorem cell_23_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c35abb6a2037ebf29698ac2277f9fb8b547ed22e672a97cc9b03df7d#256) ⟨k.val, by omega⟩)
      (0x78c09708#32, 0x1e4febc4#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_23_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000034aabf8281bd0860e3636b91bcfe8e35293672577e8e2f2fe0ba8f2a#256) ⟨k.val, by omega⟩)
      (0x8f62fc57#32, 0x435190fb#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_23_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003536415e09c63351d813d1e61952a10656e24ced2d2a4a17671d436e#256) ⟨k.val, by omega⟩)
      (0xfba29084#32, 0xde5675b1#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_23_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c80fc2c8b59bd16b5b0b8e88b6dc90aa940df9bed0a878109ae7fe8d#256) ⟨k.val, by omega⟩)
      (0x02ba8934#32, 0x8b9ba33e#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_23_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ac8f80985b5a44e6f0bb6e15f7947b41830f20c921fadb22a44a9bea#256) ⟨k.val, by omega⟩)
      (0x87af9303#32, 0x670a7fa8#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_23_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006dbfffffe28409921fdcb396815d186059405fe4fb20f826525567e0#256) ⟨k.val, by omega⟩)
      (0x53b7cdda#32, 0x365ec240#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_23_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a1b97635a813138f6d46a77d06fd3bf0ac8d503c68ceb6e3f4d45ca0#256) ⟨k.val, by omega⟩)
      (0x9f40060b#32, 0xe9e4cdec#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_23_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f67fffff7c5aa47ce4545bff92b7361fd2c4786f93ab59dfb8a7858f#256) ⟨k.val, by omega⟩)
      (0x36b284fc#32, 0xdb5ad9fc#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
