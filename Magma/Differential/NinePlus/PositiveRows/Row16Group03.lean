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

/-- Kernel-checkable real RFC Magma trajectories: input bit 16,
    output bits 24..31. -/
theorem cell_16_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000068237fff87ceacdfef63e544581c5753d390b183a49e3748e2ffcf7f#256) ⟨k.val, by omega⟩)
      (0xcc97e032#32, 0x5c780db1#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_16_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dbb17fff5c690ff79b14164a8cf5d0be5d25882bdb0ff4e08e37ffff#256) ⟨k.val, by omega⟩)
      (0x594a06a1#32, 0x6e49af50#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_16_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d1408000e83b477d652a828ecded5e242a0a797be5d4130fee000008#256) ⟨k.val, by omega⟩)
      (0x5842ec9b#32, 0x79a8455d#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_16_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000045417fff232b798585156d382426d449477fe747c20551741835df8f#256) ⟨k.val, by omega⟩)
      (0xe76cd89d#32, 0x7d29f669#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_16_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b2f4c00001954115a551d7106580fb6ec8eabb344915e617a8002008#256) ⟨k.val, by omega⟩)
      (0x1d3a79e4#32, 0x0876f8eb#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_16_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000541cc0c0a055ef504d2eb8eb850660720e53b9af709b432f81c023c0#256) ⟨k.val, by omega⟩)
      (0xc79907c9#32, 0xe3ba15a6#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_16_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d6470000458a476ad87a94018c913addb50564f5b79c0c2e90000000#256) ⟨k.val, by omega⟩)
      (0x45268513#32, 0x648ce1f5#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_16_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000db3508003f47791537b6744f11347827dd2f70d8beb179b0bbabcb4c#256) ⟨k.val, by omega⟩)
      (0xebfe3b11#32, 0xc241de1f#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
