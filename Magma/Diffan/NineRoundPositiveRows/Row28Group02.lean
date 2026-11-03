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

/-- Kernel-checkable real RFC Magma trajectories: input bit 28,
    output bits 16..23. -/
theorem cell_28_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b803c0006e602bdf783f19ba6fe52bc6f6b300c2bd74cc2acd84d000#256) ⟨k.val, by omega⟩)
      (0x19129125#32, 0xaf8ba7d8#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_28_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b1570000eb039eaceb6920dd93ae156b8fa3bd3dc5be95115d4f0000#256) ⟨k.val, by omega⟩)
      (0xb26f1066#32, 0x3b3c4f73#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_28_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b080300074a04947e27bfda30e450f8a4a88e0e3d19525e7ce74fc00#256) ⟨k.val, by omega⟩)
      (0x19e5abf8#32, 0x5cd39662#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_28_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000048080000fef8d1ec0035405305570346bbdce280974543f0178a1d08#256) ⟨k.val, by omega⟩)
      (0x2343a33d#32, 0x3749e9f5#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_28_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000100800009091867c0c3105e1c47dfe68207fe34d8a81db171a700000#256) ⟨k.val, by omega⟩)
      (0x994b4175#32, 0x81cd347f#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_28_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000080000008a758bf1b76d24ea05edc34bbaca0a782254a45dfa1900f0#256) ⟨k.val, by omega⟩)
      (0xe2b26a9d#32, 0xbd8786f8#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_28_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000030000000d2adc3a3ba6e9019469f9815166ede7bc5719031ff97c000#256) ⟨k.val, by omega⟩)
      (0x5a71bc8d#32, 0x5de75488#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_28_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cc0400001c08e510f8496799117a0923eda537bfb069dd5f3a462ea0#256) ⟨k.val, by omega⟩)
      (0x82999bba#32, 0xe143e2d4#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
