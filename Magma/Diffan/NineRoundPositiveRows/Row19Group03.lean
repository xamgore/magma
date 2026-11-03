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

/-- Kernel-checkable real RFC Magma trajectories: input bit 19,
    output bits 24..31. -/
theorem cell_19_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000045d9ffefd25adbe55691ce4891cac2f9e51658f5f32e392214bd580c#256) ⟨k.val, by omega⟩)
      (0xb6e76d63#32, 0x2c9aed16#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_19_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000040a000089f58fa615ead6f51fc3ee345a186e8c7338a3f6f98d0000#256) ⟨k.val, by omega⟩)
      (0x020c2a58#32, 0x5e07c5fa#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_19_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000049e8ffff0a3f8bb18cb43f8d4a997dd9ef60a0ae1d919d2ff25aff80#256) ⟨k.val, by omega⟩)
      (0x43b544c9#32, 0x6653fb5b#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_19_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004352ffff5cdc44935050e780363e3626f48a0319a588dcb5e7f4f8fc#256) ⟨k.val, by omega⟩)
      (0x10f8a9e1#32, 0xd623a3cc#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_19_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ecfe000076d86546fa9c3d795ad11b05851bb84cb58c628adccd5000#256) ⟨k.val, by omega⟩)
      (0xaca7419d#32, 0xe396427a#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_19_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000028e90000df5096adb038976e11e4d7c074ec953b0fedb528d0000000#256) ⟨k.val, by omega⟩)
      (0xac9f80b4#32, 0x4125e917#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_19_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002b8b0000e1760972465e4a669b0eb4ad64dd3db3a10de5e0ef0e0000#256) ⟨k.val, by omega⟩)
      (0x0de9724a#32, 0xb35364c5#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_19_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000093b50000eb040a1ef95140adf19f22f739f64ac1d94622c0494e0c6d#256) ⟨k.val, by omega⟩)
      (0xe3ed3f60#32, 0x9e826b78#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
