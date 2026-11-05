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

/-- Kernel-checkable real RFC Magma trajectories: input bit 7,
    output bits 24..31. -/
theorem cell_07_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c47f6ee2e946c07ecff9f3073de668fd8d5f6936989f151db3847809#256) ⟨k.val, by omega⟩)
      (0x176db15e#32, 0x4d72e751#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_07_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bd25e58c9f9559e50868a7e101acb6e4616e0df1fbff462b71a4c000#256) ⟨k.val, by omega⟩)
      (0xf4584189#32, 0x1d634fa6#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_07_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b9c4a91f16dcfc7fc923420c1c3204f60f9dbbe5669eb782b3d6e009#256) ⟨k.val, by omega⟩)
      (0x1c905983#32, 0x2709b20f#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_07_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003c80c92f07981e499d14b3f3441918aff4188a0e6d92061e843a0b00#256) ⟨k.val, by omega⟩)
      (0x2421e3eb#32, 0xab28d0d4#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_07_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b6a77a9f657f0bd091d463c145a0fba58bec08c4b9acfa0aeffffff8#256) ⟨k.val, by omega⟩)
      (0x95ab9a1d#32, 0x9967e80d#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_07_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000517f08b9f97c927e32ff162116110006dab80ab9d309d37c01ff8fff#256) ⟨k.val, by omega⟩)
      (0x611dc3ed#32, 0xca316152#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_07_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d913ce9c917a8169a67d13038b5f77eacbb8ef46dcf36221f2c7010c#256) ⟨k.val, by omega⟩)
      (0x01f86f6f#32, 0xdfa60316#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_07_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c29a0bdfb7e53b140d67c418895b93e5ae1297b64f0fcbddfea75e20#256) ⟨k.val, by omega⟩)
      (0x106872c7#32, 0x30db09cc#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
