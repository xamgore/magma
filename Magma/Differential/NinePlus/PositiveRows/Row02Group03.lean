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

/-- Kernel-checkable real RFC Magma trajectories: input bit 2,
    output bits 24..31. -/
theorem cell_02_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000adb24c3a12aacde3d729b81b70d97269f7965ddb2cf94b13537fcf8#256) ⟨k.val, by omega⟩)
      (0x99618734#32, 0x66d11356#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_02_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006ec6219234e41a600d28ed507300be826ce633f6a4e63316bc1c00e0#256) ⟨k.val, by omega⟩)
      (0x3b0a9264#32, 0x66299f07#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_02_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007a353545eaf3ab50d32e2e2b342174fd92a063f93b3e596f292c626c#256) ⟨k.val, by omega⟩)
      (0xcb088f1d#32, 0xe9aab3a9#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_02_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e16717e2ce0222a1ef0d37792fdf449e7c935aeca4355d76c3860f89#256) ⟨k.val, by omega⟩)
      (0x1ba61f65#32, 0x28685ad8#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_02_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c1abfcd4461cc9ce49b490747f7e7e6fe6c1fc0c62862dca5d71778d#256) ⟨k.val, by omega⟩)
      (0x34335dba#32, 0x32ab0c96#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_02_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c75497350973540a0e188a75b44b5f511e66aeb653126b31008fffc0#256) ⟨k.val, by omega⟩)
      (0x2b738078#32, 0x045ef08a#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_02_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000023df0ab1f2454c8414a84ef8546198ddb0d58237e61d53df6bc6f7d#256) ⟨k.val, by omega⟩)
      (0x1ec93ee1#32, 0x74ed7902#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_02_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a81d3dbb88714728359c549eac81f7c241f5ac3378c522f84295ade#256) ⟨k.val, by omega⟩)
      (0x8a7ba86d#32, 0x651cdfcc#32)
      (0x00000004#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
