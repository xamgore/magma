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

/-- Kernel-checkable real RFC Magma trajectories: input bit 5,
    output bits 16..23. -/
theorem cell_05_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000afb349dfd7d9eec8751e38e36dde72246dae03515c5111298d487c7e#256) ⟨k.val, by omega⟩)
      (0x25f7ed2a#32, 0xb901ba06#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_05_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004f18051f787ba29addd2664cb1c8528705f66a4071b841506e98b000#256) ⟨k.val, by omega⟩)
      (0x76a572f7#32, 0x491f036f#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_05_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000016b9352150ce83d0cf22a4a3eae6b2b75a0938c9cda46256dec9ce40#256) ⟨k.val, by omega⟩)
      (0x61731632#32, 0x0cc6c079#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_05_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e96a1ea1bf6587ffbc441991ca8e64c47470b409900e202a903cf8cf#256) ⟨k.val, by omega⟩)
      (0x4604d756#32, 0xd6f3f822#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_05_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008e41512f2675d49d6f6d4f8f3ca9a7143968e3ce644f0acf0d2b86e8#256) ⟨k.val, by omega⟩)
      (0x8ddab598#32, 0xba310c1d#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_05_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009ffd726ff830d35f907816c6ae25ebfc7bbe408a3cc6cc897bae02fb#256) ⟨k.val, by omega⟩)
      (0x9b8fad86#32, 0x49234951#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_05_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003fa04e9858fd5b9e7a49a33dba008fb36edf4b4efa87a3da8063eb00#256) ⟨k.val, by omega⟩)
      (0xb07e33fe#32, 0x54d1be3c#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_05_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000001a06130df4b488b2a4db935dcfe395bcb763726bf21b88c85700000#256) ⟨k.val, by omega⟩)
      (0x0cea4f99#32, 0x6158b0e7#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
