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

/-- Kernel-checkable real RFC Magma trajectories: input bit 31,
    output bits 16..23. -/
theorem cell_31_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f7e368c908d406e085943d6e4d7d7dd275c86a1701939b36bdb4c000#256) ⟨k.val, by omega⟩)
      (0x6607b4ec#32, 0xce371b0f#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_31_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000066a8daed77cb8283f45412a09235762f2da5931152713ce1db06be08#256) ⟨k.val, by omega⟩)
      (0xd6fe94c4#32, 0x95cbc77d#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_31_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008e55337849bd2ef051ae359e668018487675b22603a6eef4f1c20000#256) ⟨k.val, by omega⟩)
      (0xe34ada17#32, 0xc6eeb224#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_31_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000096db77796cacc70e84d6847232c7cca9b1f747e44a1c2e6836a7800d#256) ⟨k.val, by omega⟩)
      (0x8e9a5509#32, 0xc2cf689d#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_31_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a5fdb640f04d62fb681acb38509c957bf09c2541017f8c2a53b00008#256) ⟨k.val, by omega⟩)
      (0x27eb0cda#32, 0xaec1fc2e#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_31_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004521013eb90593dbc026de0b08152b74636a67c1915998e993200000#256) ⟨k.val, by omega⟩)
      (0xa6b49ca3#32, 0xe7528b76#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_31_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fba4395b7fba02789b773adf27a7e7c06c4714e40384bcf8d7500000#256) ⟨k.val, by omega⟩)
      (0xf5140481#32, 0xf9469dd4#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_31_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000035dc8af219a985570f9466364fd2e6699b2dc3f49f3295ab2690001b#256) ⟨k.val, by omega⟩)
      (0x135d7927#32, 0xdb7a28da#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
