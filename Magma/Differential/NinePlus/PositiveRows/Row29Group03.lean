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

/-- Kernel-checkable real RFC Magma trajectories: input bit 29,
    output bits 24..31. -/
theorem cell_29_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000200f8000b3543e3ab73f0e70c11f5649cb6bfe9c03ec90ea1234ef08#256) ⟨k.val, by omega⟩)
      (0xda01acfa#32, 0xcb5df9e9#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_29_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000000fff0002b826486145150b689940710be09ec569e8501cba1f30fff#256) ⟨k.val, by omega⟩)
      (0x9d16a389#32, 0x2f6e5662#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_29_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050d0000079836b70bac6fc6fea6ec5284227044616708d9bbdff0060#256) ⟨k.val, by omega⟩)
      (0xdd018cc0#32, 0x542adb00#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_29_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b00000008f6ed19275615d19aa8e124f7fbba00d7771e1df26000008#256) ⟨k.val, by omega⟩)
      (0xa0a85d39#32, 0xc20b10ba#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_29_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007c0300009493cc6da1e8c5d19c25267ad24b236aacc04d786e000800#256) ⟨k.val, by omega⟩)
      (0x6a463e95#32, 0x95610a02#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_29_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b800000051177652023bbd48cdfc18bbc0165fc2d2292ab41800a000#256) ⟨k.val, by omega⟩)
      (0x905713f2#32, 0xe55932dd#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_29_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000017e00000c9059a35d9382e23ce9d0be6d144f2eba68efc92502c0000#256) ⟨k.val, by omega⟩)
      (0x99bbe904#32, 0xb7e0f151#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_29_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003000a04027f7ebe46c93ff5c65922e92890a8b1fee6495904bbd18d6#256) ⟨k.val, by omega⟩)
      (0x4202225e#32, 0x6fba4819#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
