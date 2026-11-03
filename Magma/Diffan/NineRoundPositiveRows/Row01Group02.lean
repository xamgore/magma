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

/-- Kernel-checkable real RFC Magma trajectories: input bit 1,
    output bits 16..23. -/
theorem cell_01_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000035cbc2df270bf5881ff99c9f293bbd878aefb5b715429433ba1cffff#256) ⟨k.val, by omega⟩)
      (0xbc113a4b#32, 0x2cd40c5c#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_01_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000903efe1f226cba0dd1c9d2fecce3b9deec6ba005fd0a98b7cae69f86#256) ⟨k.val, by omega⟩)
      (0x2b903777#32, 0x32257622#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_01_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a0e7d569c489ecee35df45380baabc9f306fc346e5baafb37656bfc0#256) ⟨k.val, by omega⟩)
      (0xb38c0f6c#32, 0xe89da811#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_01_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c16e6a73c8075fa60173d43c7e298c898eec16080cc916de9d89af0c#256) ⟨k.val, by omega⟩)
      (0x91089115#32, 0xce58412c#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_01_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000855a39ff69d10202305155a37553028c230a7f6b2042067755a00000#256) ⟨k.val, by omega⟩)
      (0x5ccbe404#32, 0x8b13a771#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_01_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000de57bca6737c10cb1ed7ee423d82fae18681db1c73a0bce183f00000#256) ⟨k.val, by omega⟩)
      (0xc0de1395#32, 0x051f4c74#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_01_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008336ef9fbba0533dbab9aaafc69228ae1bbbeaf45ee916b4e38fffff#256) ⟨k.val, by omega⟩)
      (0x3ef0e287#32, 0x57ea7938#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_01_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c19381dd935137d319b4058da9153f10f345a312a4d447c49bfffc1#256) ⟨k.val, by omega⟩)
      (0xa70bf8ed#32, 0xf8d16312#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
