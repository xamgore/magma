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

/-- Kernel-checkable real RFC Magma trajectories: input bit 31,
    output bits 0..7. -/
theorem cell_31_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f874a9a6422a0c708d41ee0e99176af8cb2708f6717bfe6d8f7eb87d#256) ⟨k.val, by omega⟩)
      (0xffde7c2e#32, 0x8049915f#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_31_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f7682b725efa334baa2902a69c9f24d7fe4961f0512936c0804e0b5b#256) ⟨k.val, by omega⟩)
      (0x4c81f06b#32, 0x972a3691#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_31_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000730b59ef9b103c5380c910002f44d8f4a44681995e8ceb09248dc897#256) ⟨k.val, by omega⟩)
      (0xbd81ccfa#32, 0x51687f2a#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_31_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000b9886a9874566f800ae3c022a45799b38a238d4816ae735f13527b9#256) ⟨k.val, by omega⟩)
      (0x82e0a748#32, 0x632b49ab#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_31_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009fec830f953f3a7b2d8a8e9c05d72c0edff6d648a77993dfdc8706b0#256) ⟨k.val, by omega⟩)
      (0xfebd4cf5#32, 0x8e5f7c38#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_31_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000258e79f29fac418bc5c41b37abf52da5e54d4f0fd354c08580f21c75#256) ⟨k.val, by omega⟩)
      (0x648a4046#32, 0xe66855bd#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_31_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f6609d04fca74e2f08d5760a8ff8b1f0183f3f3f3bdac123b8c54c8f#256) ⟨k.val, by omega⟩)
      (0xd85733b4#32, 0xf5174fea#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_31_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dfe65e6cd8afa986fac70ea5d2bcebca70098c08c037653056d089c0#256) ⟨k.val, by omega⟩)
      (0x1a885551#32, 0x317c3038#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
