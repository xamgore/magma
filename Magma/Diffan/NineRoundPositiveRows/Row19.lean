module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row19Group00
public import Magma.Diffan.NineRoundPositiveRows.Row19Group01
public import Magma.Diffan.NineRoundPositiveRows.Row19Group02
public import Magma.Diffan.NineRoundPositiveRows.Row19Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 19. -/
theorem row19 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (19 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000a2db478fd37e1b8dc1f7106040e5efb4ae891dce6c87507cf2c6d48f#256,
      (0x0fa9807d#32, 0x2e5691e2#32), by simpa [oneHotDifference] using cell_19_00⟩
  · exact ⟨0x000000002216ffffa76c4c1664ccff173dafb91ee83a180a0672c53172d6af71#256,
      (0xc54b5fc2#32, 0xbc4f6270#32), by simpa [oneHotDifference] using cell_19_01⟩
  · exact ⟨0x000000008a772ff8b87115a4e27e016f8d3df54bee8bc6383b6c2fe42f3c144e#256,
      (0x3a42034f#32, 0x86b763b9#32), by simpa [oneHotDifference] using cell_19_02⟩
  · exact ⟨0x000000007ed807fff32bba681fcff7f62c278c5bd896003ef558fd0a3d36e2e8#256,
      (0xcfbda3b2#32, 0x2a5e8154#32), by simpa [oneHotDifference] using cell_19_03⟩
  · exact ⟨0x00000000d593ffc95de9629254ebe81f5f06d15de95b25a41f7498631e71e890#256,
      (0xfe4d563c#32, 0x05cd1233#32), by simpa [oneHotDifference] using cell_19_04⟩
  · exact ⟨0x000000006404ffff33fea16d63c7bbfc179fa37ed6fca410a825673a374ea76f#256,
      (0xef1eee3a#32, 0x5c54eccb#32), by simpa [oneHotDifference] using cell_19_05⟩
  · exact ⟨0x0000000092ecffd0f873871e4aad7504f006ef9a37ee6efcc8809eeff71bb8b0#256,
      (0x1744ebdb#32, 0x5240764a#32), by simpa [oneHotDifference] using cell_19_06⟩
  · exact ⟨0x000000004d22a9ffec411ccb407fc101c8a33307c2e4acb7f6d571ade7d7d590#256,
      (0xc9310fc2#32, 0xcb056c91#32), by simpa [oneHotDifference] using cell_19_07⟩
  · exact ⟨0x000000006477ffffea04720e69e2fe0d6478191adb6fcd97e366dfd27de9fd87#256,
      (0x4c94c463#32, 0x3d7ed427#32), by simpa [oneHotDifference] using cell_19_08⟩
  · exact ⟨0x00000000039cffffd61c398ec7ffb1b83fc5d7d9a0d4f32fabdcd4999e8d51fc#256,
      (0xb473f29b#32, 0xb65a94b7#32), by simpa [oneHotDifference] using cell_19_09⟩
  · exact ⟨0x00000000f035ffff4b15d6dd2d75c2e93349f7246c6980c7f4d7a54ee866f9fe#256,
      (0x03abdfcd#32, 0xb92fb924#32), by simpa [oneHotDifference] using cell_19_10⟩
  · exact ⟨0x0000000052e70fffb56cd06d659940ce1f32b616efc62021ef88bd43d752594a#256,
      (0x4f945b22#32, 0x07f68b2d#32), by simpa [oneHotDifference] using cell_19_11⟩
  · exact ⟨0x00000000511d0000677b64e4c65944ee6a45654834808641683eabd188003000#256,
      (0x1797f1a1#32, 0x73faa99e#32), by simpa [oneHotDifference] using cell_19_12⟩
  · exact ⟨0x0000000063a5fffffeef56594c4b4845abda91c7cb7ff2972bc5e2a32a012fe0#256,
      (0xc044ea23#32, 0x5fa711a1#32), by simpa [oneHotDifference] using cell_19_13⟩
  · exact ⟨0x00000000611cffff9c38e11f61fa8ddc6e9730dd87ce2ba7b99e1c67b03c2c00#256,
      (0x248196c3#32, 0xaf90d7b5#32), by simpa [oneHotDifference] using cell_19_14⟩
  · exact ⟨0x000000004ed7fe2ffd231b5e3ca3d8f541826e55dc61ab5ec1f621a653629ed0#256,
      (0xabe5aa9b#32, 0xba5b43cb#32), by simpa [oneHotDifference] using cell_19_15⟩
  · exact ⟨0x00000000d7a4adeede0d544f73fcee2d69185014975825fc979c1d430589af8e#256,
      (0x1a285d89#32, 0x0a8b58bd#32), by simpa [oneHotDifference] using cell_19_16⟩
  · exact ⟨0x00000000f517fad9f9b0b3c0e400d9982d15c14e602d09228cb6d328ffcb0000#256,
      (0x593a1b37#32, 0x42d48652#32), by simpa [oneHotDifference] using cell_19_17⟩
  · exact ⟨0x000000008d4777f95351c7d4e9ebf4de8318042221c32aedfaa5a3370eaaf0f0#256,
      (0xd6a06b06#32, 0x9abf1473#32), by simpa [oneHotDifference] using cell_19_18⟩
  · exact ⟨0x00000000efa90000290f4207c2afe564f5b8f608fdd8b34128b7a35332e70000#256,
      (0x93e55014#32, 0xa46d8a28#32), by simpa [oneHotDifference] using cell_19_19⟩
  · exact ⟨0x000000002e66fdffbd4fe34e60de677d231cdbbd07cc2c94ee04fe9f6de8ff80#256,
      (0xd98d68ae#32, 0xed5991b8#32), by simpa [oneHotDifference] using cell_19_20⟩
  · exact ⟨0x000000007895ffff5dbade53763c37332f130d4152baa07674f25c045ee6fdbc#256,
      (0xc3c78e5b#32, 0xfed182cc#32), by simpa [oneHotDifference] using cell_19_21⟩
  · exact ⟨0x000000008ef8ff007fd4ebf2fc7631707f6d77d1979f0b1e85ca6c1f47900000#256,
      (0xadc5fe38#32, 0x90f0e3d6#32), by simpa [oneHotDifference] using cell_19_22⟩
  · exact ⟨0x0000000076ed00004c53ef1c4c64745957117f90b3c046e214aab19d01900008#256,
      (0x97befc4d#32, 0x32f28e70#32), by simpa [oneHotDifference] using cell_19_23⟩
  · exact ⟨0x0000000045d9ffefd25adbe55691ce4891cac2f9e51658f5f32e392214bd580c#256,
      (0xb6e76d63#32, 0x2c9aed16#32), by simpa [oneHotDifference] using cell_19_24⟩
  · exact ⟨0x00000000040a000089f58fa615ead6f51fc3ee345a186e8c7338a3f6f98d0000#256,
      (0x020c2a58#32, 0x5e07c5fa#32), by simpa [oneHotDifference] using cell_19_25⟩
  · exact ⟨0x0000000049e8ffff0a3f8bb18cb43f8d4a997dd9ef60a0ae1d919d2ff25aff80#256,
      (0x43b544c9#32, 0x6653fb5b#32), by simpa [oneHotDifference] using cell_19_26⟩
  · exact ⟨0x000000004352ffff5cdc44935050e780363e3626f48a0319a588dcb5e7f4f8fc#256,
      (0x10f8a9e1#32, 0xd623a3cc#32), by simpa [oneHotDifference] using cell_19_27⟩
  · exact ⟨0x00000000ecfe000076d86546fa9c3d795ad11b05851bb84cb58c628adccd5000#256,
      (0xaca7419d#32, 0xe396427a#32), by simpa [oneHotDifference] using cell_19_28⟩
  · exact ⟨0x0000000028e90000df5096adb038976e11e4d7c074ec953b0fedb528d0000000#256,
      (0xac9f80b4#32, 0x4125e917#32), by simpa [oneHotDifference] using cell_19_29⟩
  · exact ⟨0x000000002b8b0000e1760972465e4a669b0eb4ad64dd3db3a10de5e0ef0e0000#256,
      (0x0de9724a#32, 0xb35364c5#32), by simpa [oneHotDifference] using cell_19_30⟩
  · exact ⟨0x0000000093b50000eb040a1ef95140adf19f22f739f64ac1d94622c0494e0c6d#256,
      (0xe3ed3f60#32, 0x9e826b78#32), by simpa [oneHotDifference] using cell_19_31⟩

end Magma.DiffanNineRoundPositiveRows
