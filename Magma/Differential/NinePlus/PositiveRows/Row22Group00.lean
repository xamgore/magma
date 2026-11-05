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

/-- Kernel-checkable real RFC Magma trajectories: input bit 22,
    output bits 0..7. -/
theorem cell_22_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000acc264fd3dbdc4bc1ff5a28e1fc3a2f285ed35680ba87c91adfd3691#256) ⟨k.val, by omega⟩)
      (0xa525f364#32, 0xf4ce0700#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_22_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000013fffffda354c1a3759be841dae29d94de90872f2bd9fcde8773f49#256) ⟨k.val, by omega⟩)
      (0x4040d1ea#32, 0xb7924388#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_22_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000062977f3cf888750016b2904b5c13f663ad0313770606898e2df183b4#256) ⟨k.val, by omega⟩)
      (0xf5086440#32, 0xcb2c9ac9#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_22_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000077dfffffba61eb673c6801bbc6ea367c0fbaf6ce25dd654b65db2823#256) ⟨k.val, by omega⟩)
      (0x34dc5048#32, 0xe4e1ed74#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_22_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000872c6cfe11363be7818a9e2c218446ed7cfb7f401064206ef304e411#256) ⟨k.val, by omega⟩)
      (0x35fffdeb#32, 0x3cd2a335#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_22_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003830fffdfefa110b871b97fa669d1adbab7fbdf1529cc23423002d58#256) ⟨k.val, by omega⟩)
      (0xc600fe18#32, 0xbaa94a0f#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_22_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000053b13fdb69bd42e1a2c03c2057bd2f9907a46ddbda069f1f7bd10470#256) ⟨k.val, by omega⟩)
      (0x2ef6a735#32, 0x1254b618#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_22_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bc1000007d32a95a5416cf022fe6a2c072009c62d379ea7b1c1437a0#256) ⟨k.val, by omega⟩)
      (0x06a19df9#32, 0xf458a4c6#32)
      (0x00400000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
