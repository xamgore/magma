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

/-- Kernel-checkable real RFC Magma trajectories: input bit 23,
    output bits 24..31. -/
theorem cell_23_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c4600000aa52642dbbedde34441670d2b75bcd88927abe21e9800000#256) ⟨k.val, by omega⟩)
      (0x9b38b54e#32, 0xa894301c#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_23_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000077b800000ddb7158f74c0934b8fd86173667c759cb460d5b85000000#256) ⟨k.val, by omega⟩)
      (0xd14d40cf#32, 0xe6585699#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_23_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000006b80000a6538f5b176693bbbfe239bf9113850ed54db3c7cb000080#256) ⟨k.val, by omega⟩)
      (0x98c83ae1#32, 0x35fd3383#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_23_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000e80000099a23d42f91bba1724d057f94ec42f3fd6713a3c27f00000#256) ⟨k.val, by omega⟩)
      (0xc3f55ac6#32, 0x98945a64#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_23_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c7b00000b9ab8daa63a49c5a3e2e7f121faee3397cdac96a2c03090b#256) ⟨k.val, by omega⟩)
      (0x1b28e8b1#32, 0x2e6e7cdd#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_23_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b8200000e9a526c0673a4df5c1abb2cd2a95b3834b498ce8b0cf0000#256) ⟨k.val, by omega⟩)
      (0x8c58b2b2#32, 0xe4618b63#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_23_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b3b00000c954f34ebabb3c31a1a5a695ce5fa9cdf1a7f33c5847ffd0#256) ⟨k.val, by omega⟩)
      (0x7b081da7#32, 0x49d3d1c7#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_23_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000347c000050a523285576abd30e400ab87b5c7308ef4266f0f2d1ea78#256) ⟨k.val, by omega⟩)
      (0x706a3057#32, 0x59856a76#32)
      (0x00800000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
