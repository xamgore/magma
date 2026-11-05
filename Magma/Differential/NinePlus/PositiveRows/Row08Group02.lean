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

/-- Kernel-checkable real RFC Magma trajectories: input bit 8,
    output bits 16..23. -/
theorem cell_08_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000083779b7f67b91516d23268d02aac039e8f8499e5fac8dd9acaa0fff8#256) ⟨k.val, by omega⟩)
      (0x86979bde#32, 0x356151fe#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_08_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000060a893f6434f65663e7e8861f171833ca292d9b84284a67f63e7fcf#256) ⟨k.val, by omega⟩)
      (0x6cca6c9a#32, 0x86f65d9d#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_08_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b8eed6ceb92146167b86b0c7c1ce84489e739efdf7d1ca9c790c3810#256) ⟨k.val, by omega⟩)
      (0xc282ea81#32, 0x1056f4b9#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_08_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002056a2ffdb7ceb6f4432da4e85b5d3deb373f2d88956ccdb51f6ff0f#256) ⟨k.val, by omega⟩)
      (0x981b27bb#32, 0xb3af6eae#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_08_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000037e92cff1fd5f42b6d1b9d101bf1be2882a77a396564189d452a1fff#256) ⟨k.val, by omega⟩)
      (0xbb225634#32, 0xe0c7a34c#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_08_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000079ea7700258435eeaeffe6f07a60af5283115034567fe5d9a4180050#256) ⟨k.val, by omega⟩)
      (0xe5d944b9#32, 0x6d9d4147#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_08_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fb51f51110d06924958afdf944bb2a6e74d0e32552e0cefaf72c23c0#256) ⟨k.val, by omega⟩)
      (0x407daca6#32, 0x2964c6b1#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_08_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000700814ffefc989011cccc43fa4b2f6ffe3c8a57e0d63f03633dcfffe#256) ⟨k.val, by omega⟩)
      (0x2a233884#32, 0x10c3fb44#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
