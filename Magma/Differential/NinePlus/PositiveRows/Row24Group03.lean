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

/-- Kernel-checkable real RFC Magma trajectories: input bit 24,
    output bits 24..31. -/
theorem cell_24_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000250800003a33f43a24f5d895ac4c370083721531d039c9e7db000000#256) ⟨k.val, by omega⟩)
      (0xbf86d1b1#32, 0x56edf585#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_24_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fac800000cabe5af6fa0f41afff1dc24e151bdc5e69a80fab104e000#256) ⟨k.val, by omega⟩)
      (0x9afbe016#32, 0x67c24b29#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_24_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000378080004c6bb6487a480cfb6ddc645eca39a1e9e084ef10510b0000#256) ⟨k.val, by omega⟩)
      (0x8965619b#32, 0xff06683f#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_24_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b680000095dac0389de8c7384239d7aaddf6379e4078fca4b4400000#256) ⟨k.val, by omega⟩)
      (0x38e3ec80#32, 0xf35f7c47#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_24_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d2afff00c60aa5ea1e2d025c024f62df860e7293474b9cbd40640020#256) ⟨k.val, by omega⟩)
      (0x373e91c5#32, 0x005e0b02#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_24_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000388800007465847a6719afc0e14407f29757481684911afffc11780f#256) ⟨k.val, by omega⟩)
      (0x7574bee6#32, 0x3a6b8ac8#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_24_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008eff1000201023c32841fff15c4948c58bf10260a2b2de23d8460004#256) ⟨k.val, by omega⟩)
      (0x29e48c7b#32, 0x1981209e#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_24_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000075d700002705faea4b6146fdbda1f843ab495d5e292373cc320ebe22#256) ⟨k.val, by omega⟩)
      (0xd0690add#32, 0xb3f5af81#32)
      (0x01000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
