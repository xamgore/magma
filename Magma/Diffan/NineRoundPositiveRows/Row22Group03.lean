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

/-- Kernel-checkable real RFC Magma trajectories: input bit 22,
    output bits 24..31. -/
theorem cell_22_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f47800002571462a77e6863a02daf6ad8b3a43208c61d22daac00080#256) ⟨k.val, by omega⟩)
      (0xf5a55544#32, 0xd84f4930#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_22_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002cb000005d62bb356a16f99e58594a5d898c6a9e2710b7880638b000#256) ⟨k.val, by omega⟩)
      (0xf1cf5589#32, 0xd45eb4c5#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_22_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ea100000a004ac8dba153ac1ebe65c64dd0abac8145355e7d6000000#256) ⟨k.val, by omega⟩)
      (0xe82178a0#32, 0x32daf4be#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_22_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009a100000ae54755249699949f0e00d30f5878002786cae2f1bc00000#256) ⟨k.val, by omega⟩)
      (0xb1fc8413#32, 0xe2bb1f19#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_22_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000536000009ac33c13dbcc6b085084090c67779bd17e4064f120000008#256) ⟨k.val, by omega⟩)
      (0xa720cb57#32, 0xf611878d#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_22_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000ad00000076a29698ce167f4e9d818c08d84cec96e1b72b8d0000000#256) ⟨k.val, by omega⟩)
      (0x58a23b03#32, 0xbd60fb98#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_22_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000053600000c709a90afd4d1a65920989d438e98d6dca64ca90bc773d00#256) ⟨k.val, by omega⟩)
      (0x65e5cc0f#32, 0xb20a4eef#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_22_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a0700000520c33712a2c6f16a3870955bdaa9ee1833066a0582d2c27#256) ⟨k.val, by omega⟩)
      (0x147f89bb#32, 0x7eaa8596#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
