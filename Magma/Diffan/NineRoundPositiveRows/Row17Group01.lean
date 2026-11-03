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

/-- Kernel-checkable real RFC Magma trajectories: input bit 17,
    output bits 8..15. -/
theorem cell_17_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d8f53fff5ec91da422eeeddee1031e4d88dc425a7347c3da95011efe#256) ⟨k.val, by omega⟩)
      (0x4ad93b4e#32, 0xcc01f6b0#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_17_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003e607ffec879e63d235dda70a0e9e2692db5601fa4923f970aa63e0b#256) ⟨k.val, by omega⟩)
      (0x2ef2efb4#32, 0x3388a758#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_17_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ae223f52b52ecae06f3bb5e1a33067de5a1617dbc4405c5eee0c319c#256) ⟨k.val, by omega⟩)
      (0x061bd6b1#32, 0x919e634c#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_17_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006becfffff8520fedc0dcd46c744208b9b7daaba5115678638b477382#256) ⟨k.val, by omega⟩)
      (0x234b3d05#32, 0xc222d169#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_17_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002c55ffffd8487360ea905646ab10499dbcc3cdf197865b5d2aacef78#256) ⟨k.val, by omega⟩)
      (0xdb1ef717#32, 0xfb7c3ecd#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_17_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bc2cffffee2e5b079af7680612fe7336b2c37ab24b206d40347fb002#256) ⟨k.val, by omega⟩)
      (0x50b6fbfa#32, 0x1f8d7c56#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_17_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002215fffff29aad3cfc2e01f3fc6d78c19de7943bc4943ecc1f37d704#256) ⟨k.val, by omega⟩)
      (0xa5a7385a#32, 0xe9ca9d47#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_17_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000716a01ff6e4ae1ab51aa39b3c4933e3c3d680948e4c0c3ee190d7d85#256) ⟨k.val, by omega⟩)
      (0x2558f317#32, 0x2d918d7f#32)
      (0x00020000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
