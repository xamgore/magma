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

/-- Kernel-checkable real RFC Magma trajectories: input bit 10,
    output bits 16..23. -/
theorem cell_10_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a6cac00e52c146ff30699037d7d46a8108084faa00116033fd2b400#256) ⟨k.val, by omega⟩)
      (0xbb5a19f0#32, 0x7d9c4d27#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_10_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000519773f08cbffb3ea5c6c2d6921036d216db05203a5c181e7dc0ffdf#256) ⟨k.val, by omega⟩)
      (0x75a9e459#32, 0x55d7832a#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_10_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000855c8a513ebd730187328f71de373fbdf2a9dc633c897650c0d40187#256) ⟨k.val, by omega⟩)
      (0x2f8e3434#32, 0x15bba259#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_10_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c40932ffae9e348404694f1f7093346feb50d62c04bf1ee02c7bffff#256) ⟨k.val, by omega⟩)
      (0xa2350ba7#32, 0x69ecc3b9#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_10_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004a445cffdfb390c009945b5c608ebdd066990ad00d1a76cd27777fff#256) ⟨k.val, by omega⟩)
      (0xfbbac2d5#32, 0x30a50f20#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_10_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000830dc43e112ba83095103878bb72fcb380daa32ed3690a56f4961080#256) ⟨k.val, by omega⟩)
      (0x540a9efa#32, 0xcff24581#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_10_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f1ef90ff17bbf76e56c7acaa9479e75eb6d0dcffb801146b002fffff#256) ⟨k.val, by omega⟩)
      (0x9c929ff5#32, 0x08f93f68#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_10_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000080653f0073cb5cfd480411952fb9ed79baaa24b4c116b974b6a40000#256) ⟨k.val, by omega⟩)
      (0x71e7c18f#32, 0xff17055c#32)
      (0x00000400#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
