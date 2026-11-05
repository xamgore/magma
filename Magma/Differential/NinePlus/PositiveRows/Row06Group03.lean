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

/-- Kernel-checkable real RFC Magma trajectories: input bit 6,
    output bits 24..31. -/
theorem cell_06_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e0fe36104197f8462f1ae8de82d70bfd54c4d02280285d36a408800f#256) ⟨k.val, by omega⟩)
      (0xbbc6436b#32, 0x5214e8ff#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_06_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000301a241051e24a32165ad50c19b63f24c12c2c204609d1705f00000e#256) ⟨k.val, by omega⟩)
      (0xaae386b6#32, 0xa5951f76#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_06_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000045f48fbff0a774315a40b053fdf5811e40fcb46bfc55f9f58cfffcff#256) ⟨k.val, by omega⟩)
      (0x3d710121#32, 0xf153d5a8#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_06_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003b3a2daf4373fbf7b21f0b27dd7de2fa7cd92f8d1f20ca8b55bc0b00#256) ⟨k.val, by omega⟩)
      (0x16014e31#32, 0x6af35e4d#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_06_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000050e9553fcb7453beb186f89effa3ea756fad3aa702139f5facfb007c#256) ⟨k.val, by omega⟩)
      (0x98ff7644#32, 0xcb2e6736#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_06_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000095ada2b0ee1e629013e278dbf7581aca27b44bcb24d38b9c10180040#256) ⟨k.val, by omega⟩)
      (0x6468bdbb#32, 0x0910aa60#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_06_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000070eb8428588b3e2a2169d70eaac785689da9a33ed3948d9046abd400#256) ⟨k.val, by omega⟩)
      (0x4a283b26#32, 0x0b5c9019#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_06_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000964ea33fc119f6fcea8c9485887d2a1b3db9cd1acd3afc29816cb56c#256) ⟨k.val, by omega⟩)
      (0xb00f7d6d#32, 0x7767fa71#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
