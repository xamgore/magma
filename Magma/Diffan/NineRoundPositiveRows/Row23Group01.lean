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
    output bits 8..15. -/
theorem cell_23_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f77fffffaaef45f7b6978b590a2ac308d0bd467a0cfb96f82e6f8d07#256) ⟨k.val, by omega⟩)
      (0x75967451#32, 0xf899fd14#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_23_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bc87ffffb5e75c37b3c9ea29ed4d87c305fe57943af37afb6721b502#256) ⟨k.val, by omega⟩)
      (0xd548df26#32, 0xa6c34941#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_23_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002ca1e4c66f8157201e0ae16e4fc5a73fa083ff2582e3f4ef4716ed00#256) ⟨k.val, by omega⟩)
      (0x520fef36#32, 0xd0adcbb9#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_23_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000063a7ffff2f03c89355e6fcd80df4519f9e136cf02554e72e67b46511#256) ⟨k.val, by omega⟩)
      (0x55800a58#32, 0x06e59b8d#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_23_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003240ff6f5218b74385ec40fe62bf2ef8ab540d353f5c5bda243fb700#256) ⟨k.val, by omega⟩)
      (0x0948d13a#32, 0x1f48e4c9#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_23_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000215ffff8ce5b6137904bf99935fed1b1960f84d35870e82938e6600f#256) ⟨k.val, by omega⟩)
      (0x365f0160#32, 0x53d13e29#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_23_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007d6fffff11c199c7b0f87992c4b281872f83294b490ed6c1cc9c10fe#256) ⟨k.val, by omega⟩)
      (0x44c9640d#32, 0x1f4d823f#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_23_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cc47fffd4e4c2bb03e939f60028b4921c4d6cb065ee9f8289478e07#256) ⟨k.val, by omega⟩)
      (0xef5ba0ff#32, 0x6b3c8083#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
