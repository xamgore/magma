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

/-- Kernel-checkable real RFC Magma trajectories: input bit 19,
    output bits 0..7. -/
theorem cell_19_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a2db478fd37e1b8dc1f7106040e5efb4ae891dce6c87507cf2c6d48f#256) ⟨k.val, by omega⟩)
      (0x0fa9807d#32, 0x2e5691e2#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_19_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002216ffffa76c4c1664ccff173dafb91ee83a180a0672c53172d6af71#256) ⟨k.val, by omega⟩)
      (0xc54b5fc2#32, 0xbc4f6270#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_19_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008a772ff8b87115a4e27e016f8d3df54bee8bc6383b6c2fe42f3c144e#256) ⟨k.val, by omega⟩)
      (0x3a42034f#32, 0x86b763b9#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_19_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007ed807fff32bba681fcff7f62c278c5bd896003ef558fd0a3d36e2e8#256) ⟨k.val, by omega⟩)
      (0xcfbda3b2#32, 0x2a5e8154#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_19_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d593ffc95de9629254ebe81f5f06d15de95b25a41f7498631e71e890#256) ⟨k.val, by omega⟩)
      (0xfe4d563c#32, 0x05cd1233#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_19_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006404ffff33fea16d63c7bbfc179fa37ed6fca410a825673a374ea76f#256) ⟨k.val, by omega⟩)
      (0xef1eee3a#32, 0x5c54eccb#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_19_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000092ecffd0f873871e4aad7504f006ef9a37ee6efcc8809eeff71bb8b0#256) ⟨k.val, by omega⟩)
      (0x1744ebdb#32, 0x5240764a#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_19_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004d22a9ffec411ccb407fc101c8a33307c2e4acb7f6d571ade7d7d590#256) ⟨k.val, by omega⟩)
      (0xc9310fc2#32, 0xcb056c91#32)
      (0x00080000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
