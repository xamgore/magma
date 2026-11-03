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

/-- Kernel-checkable real RFC Magma trajectories: input bit 26,
    output bits 8..15. -/
theorem cell_26_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000554f5fffe8f53bfa7deceead811e52da072cd614f600659920a65c80#256) ⟨k.val, by omega⟩)
      (0x1f4503bf#32, 0x29fdb8cd#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_26_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002d000000a93fd970c00ef0d8fa04aff90d9717dbd2afc42dd9727200#256) ⟨k.val, by omega⟩)
      (0x6836565f#32, 0x11ba298c#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_26_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d1ffffff1dc673bc14c9f604ccebffe6c4497fd2ebbfde2c8e882d98#256) ⟨k.val, by omega⟩)
      (0xf1403d13#32, 0xfb9a80aa#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_26_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b66fffffcb1fd910eeb88e153b802042c07adb83431e7eacba6f2e7c#256) ⟨k.val, by omega⟩)
      (0x1ed6e833#32, 0x60f6133d#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_26_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000082fcffff105e4d15bd2b6219263d6bb92cd38d39994ea3d6ae9f2c00#256) ⟨k.val, by omega⟩)
      (0xafb4efb0#32, 0xe20893ed#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_26_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000f000000f933c640adf98988c3d5f7135482d49cff570688c0ec9900#256) ⟨k.val, by omega⟩)
      (0xb74e0da8#32, 0x366d6422#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_26_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bd000000c0f1dca392682d6f4d1c0457f1a6b548ed1114e78b94d000#256) ⟨k.val, by omega⟩)
      (0xab7136a7#32, 0x0cdad8f2#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_26_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c2f439fadd99aa1422ffa709219e333b096df349357db503ce852200#256) ⟨k.val, by omega⟩)
      (0x43f1cc6d#32, 0x8a97b718#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
