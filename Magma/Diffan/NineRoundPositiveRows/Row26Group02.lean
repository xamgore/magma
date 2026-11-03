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
    output bits 16..23. -/
theorem cell_26_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000030000001e324528368ecfa0d117ed59f410f513b59875bc88230000#256) ⟨k.val, by omega⟩)
      (0x0f7bfe24#32, 0x9e464ca2#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_26_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005b845500b5f2c252ee43ebe9f6d0267ddff67fc062c989e5560e0003#256) ⟨k.val, by omega⟩)
      (0x1734e3c5#32, 0xd2238dc5#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_26_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000e000000e0ef1bac3fe2a47bef51f23ed48695dc7c1f5d6e82bb0000#256) ⟨k.val, by omega⟩)
      (0xe6f7a628#32, 0x5c754d66#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_26_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004f000000b363f29dfff0891fb872ddf5b6978dbd8c4939e3e6d70000#256) ⟨k.val, by omega⟩)
      (0x07b62e2b#32, 0xdb8d7202#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_26_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ca0000005b794d3b8d97c1c7b86d804528645939e805abed0fb00000#256) ⟨k.val, by omega⟩)
      (0x736a87c5#32, 0xd39ecd03#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_26_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d87507763a3f8468723b58507291abf8b4bc39de0829239f39601000#256) ⟨k.val, by omega⟩)
      (0x2c002a47#32, 0x35e78216#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_26_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c3c00000df99391eba169fd3be880cdaa78a7447384a653c95304000#256) ⟨k.val, by omega⟩)
      (0xfe0ea0fb#32, 0x13239362#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_26_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000081000000a70aed886f7e1c3c0a4ded175f5566b78bc89d396f800000#256) ⟨k.val, by omega⟩)
      (0x34b9802d#32, 0xc9e56ea9#32)
      (0x04000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
