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

/-- Kernel-checkable real RFC Magma trajectories: input bit 28,
    output bits 24..31. -/
theorem cell_28_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ffe00005653ddb2841740c4cd7e34d7f087871d203384cf92eef000#256) ⟨k.val, by omega⟩)
      (0x63b2fe92#32, 0xfbc346ea#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_28_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b0800000de0552be38cdc6474c09cbfe8ab7759c68936af5818f8000#256) ⟨k.val, by omega⟩)
      (0x78fa593e#32, 0x91cf2ad9#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_28_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e00f8000cad9c370bb911fc927f081c32fa35ef6619989d3caa00009#256) ⟨k.val, by omega⟩)
      (0xe0248e52#32, 0x5dd6aaad#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_28_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000038000000e308486b3a257de2c1a5d96634ff538a1eaf3cad87000000#256) ⟨k.val, by omega⟩)
      (0xcfcd6693#32, 0x799e55b9#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_28_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006008300030a4d4c8ac60baa939b5e5d6270631975f641d7a5000fc00#256) ⟨k.val, by omega⟩)
      (0x3f442121#32, 0x48c61718#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_28_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000680000007fa37362144093f987d7f9a0f913705206ccb21340000001#256) ⟨k.val, by omega⟩)
      (0xf5ae50ac#32, 0x5b65e495#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_28_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000070000000f328c90c88f024cff96ab0474a8074da0e153f6170000040#256) ⟨k.val, by omega⟩)
      (0xf5ab6b48#32, 0x84d970b8#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_28_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005888200004ec637a598bfae3d8fddfd5021c858d114abcaca79e036c#256) ⟨k.val, by omega⟩)
      (0xbc55d99e#32, 0x3f728922#32)
      (0x10000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
