module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row00Group00
public import Magma.Diffan.NineRoundPositiveRows.Row00Group01
public import Magma.Diffan.NineRoundPositiveRows.Row00Group02
public import Magma.Diffan.NineRoundPositiveRows.Row00Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 0. -/
theorem row00 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (0 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000000486095bee1b7f91f0eda9921cfa82cb7723eabd878c61ed23f259f7#256,
      (0xcfc325c2#32, 0xb7e4fa64#32), by simpa [oneHotDifference] using cell_00_00⟩
  · exact ⟨0x00000000866badbba042df7637b48fab5935cf8c54d2dfb874975b405faee9bf#256,
      (0x70053ffa#32, 0xef2bf42a#32), by simpa [oneHotDifference] using cell_00_01⟩
  · exact ⟨0x00000000b8436ec55713a24945f9d8be6cb948ace11fb2b2d40c5373fc09a92b#256,
      (0x135fc2bf#32, 0x1b46ec04#32), by simpa [oneHotDifference] using cell_00_02⟩
  · exact ⟨0x00000000c8586999ba6d2aeefac785623a01415809949bb6eea6cd08bfd524b8#256,
      (0xbadc3a1c#32, 0x6837a0b5#32), by simpa [oneHotDifference] using cell_00_03⟩
  · exact ⟨0x000000007c6a78414a31f427fb76492e2b0f2810a9efd86c619c36699bd2a157#256,
      (0x6deb7026#32, 0x9ed904f4#32), by simpa [oneHotDifference] using cell_00_04⟩
  · exact ⟨0x000000001b2f8d3f88ede5c81857592e1e895c0254637d48725d9845a6a54d1c#256,
      (0x8cf4a508#32, 0x95529b44#32), by simpa [oneHotDifference] using cell_00_05⟩
  · exact ⟨0x00000000d9f54c85e00c76393acce119fae79b4deaccfcd8f6d5fb53b6d01ca6#256,
      (0xbb71d24d#32, 0xf425a500#32), by simpa [oneHotDifference] using cell_00_06⟩
  · exact ⟨0x000000003ab32499d3cc003e7243dc78eb6af17eb958635d08962d29fc4668d0#256,
      (0x17c0f758#32, 0x6f1f5105#32), by simpa [oneHotDifference] using cell_00_07⟩
  · exact ⟨0x0000000050392a3d321c69789d44c6c3bda0654e0bbf1f8f696547cbe1ff76fc#256,
      (0x227e3747#32, 0x5b41fa80#32), by simpa [oneHotDifference] using cell_00_08⟩
  · exact ⟨0x00000000a884d343f04e66103db19eaef9f484bf4f17b3f9d00689cbb6730600#256,
      (0xc9c1055a#32, 0x77e54aa5#32), by simpa [oneHotDifference] using cell_00_09⟩
  · exact ⟨0x00000000cd1558918a27d5b699f2a228ffed3d844e07f83729785f29d2f38c38#256,
      (0xfaff508e#32, 0x97be1ec8#32), by simpa [oneHotDifference] using cell_00_10⟩
  · exact ⟨0x0000000098276b6d7d9d604e59b0322b086fd632bd48281e745d3b89e8a88d04#256,
      (0x32236730#32, 0x19ce35b8#32), by simpa [oneHotDifference] using cell_00_11⟩
  · exact ⟨0x00000000f1beef0be09145c2f75373ef084b7796dfee5b7184946c3c9d80af80#256,
      (0x140d3ef2#32, 0xdb6710a5#32), by simpa [oneHotDifference] using cell_00_12⟩
  · exact ⟨0x000000005bb2e9516d9f8a68562741a16659452ecdce210d5150409f08820fc0#256,
      (0xe2ed6eca#32, 0x47464bee#32), by simpa [oneHotDifference] using cell_00_13⟩
  · exact ⟨0x00000000b33a47098a348e6b72f3216b4df790009df89a6ca4c7a3a79295d000#256,
      (0xd44f21ce#32, 0x685960cb#32), by simpa [oneHotDifference] using cell_00_14⟩
  · exact ⟨0x00000000b6b5a613acfb7c1bb9993c0f14b06ab30c2a8dfd776cadc63ea44000#256,
      (0xcf6bb537#32, 0xca909f3a#32), by simpa [oneHotDifference] using cell_00_15⟩
  · exact ⟨0x00000000cedf44cf4f66bf8ffff8e9655bb3131ec1bfd89f05297e69a794b6a0#256,
      (0x3f310d74#32, 0xd0770432#32), by simpa [oneHotDifference] using cell_00_16⟩
  · exact ⟨0x00000000b4d6a7d3628e260b4b5e7539b0edcc551d8b7facc33ba2e78cb6f690#256,
      (0xa4559910#32, 0xff77dd49#32), by simpa [oneHotDifference] using cell_00_17⟩
  · exact ⟨0x000000001da0c7cf1efeb27bfb80a5492fd763e3b805f796889743031e296a5c#256,
      (0x084e044c#32, 0x687ed32b#32), by simpa [oneHotDifference] using cell_00_18⟩
  · exact ⟨0x00000000b3822b53ca846177f86f7e5a2954f3c96545d901ab44636e446bcf8f#256,
      (0x070addfc#32, 0xfd593c9f#32), by simpa [oneHotDifference] using cell_00_19⟩
  · exact ⟨0x00000000f5ec7b513c57141b72c3a398e6ec69f89b18ac457b837dbb644fe070#256,
      (0x52a6fb5a#32, 0x91a03e5e#32), by simpa [oneHotDifference] using cell_00_20⟩
  · exact ⟨0x000000007bd7a2ad3c155483a565a9db0f3cd3266a106ea6e25ce8d20ddb402f#256,
      (0x7b098035#32, 0xa712db36#32), by simpa [oneHotDifference] using cell_00_21⟩
  · exact ⟨0x00000000a084fe0146b9a9e9b384a8bc8fa618985fe3848ff71ac1608d330083#256,
      (0x9ae543e5#32, 0x8ec8f179#32), by simpa [oneHotDifference] using cell_00_22⟩
  · exact ⟨0x0000000029371083690dc0ed50fc3de13a378c131a2703f9362a650cb689ff81#256,
      (0xeae2f701#32, 0x484ce0ad#32), by simpa [oneHotDifference] using cell_00_23⟩
  · exact ⟨0x000000005b77fa51aadc790fb21df5309bb78deb0112905a082db13406800000#256,
      (0x0ea0fa62#32, 0x9580028e#32), by simpa [oneHotDifference] using cell_00_24⟩
  · exact ⟨0x00000000449be821407289ddd73633d8e5fa4c6cbe363bff964fd95b44fff807#256,
      (0x90bb5a92#32, 0xa5a18097#32), by simpa [oneHotDifference] using cell_00_25⟩
  · exact ⟨0x0000000016f1e635c3f22c02a387844394df68c2721734f723f2dbbdec67e200#256,
      (0xba5a2a9d#32, 0xbded7612#32), by simpa [oneHotDifference] using cell_00_26⟩
  · exact ⟨0x00000000d6a693db058f9735e212abc3f3c42d46798e751884d943c4427d8080#256,
      (0xef291c3c#32, 0x4eb878e8#32), by simpa [oneHotDifference] using cell_00_27⟩
  · exact ⟨0x0000000082be9a336f240349f4fd3b7e07b0d3d597da3efa733e76392fffffff#256,
      (0xcfeffcbf#32, 0xf13fb2dd#32), by simpa [oneHotDifference] using cell_00_28⟩
  · exact ⟨0x00000000935c67410dfc2d6c4257f2394a0ae6c161a3c6c7a310abb7f0b9ccd6#256,
      (0xdcb298e8#32, 0x4d1f542c#32), by simpa [oneHotDifference] using cell_00_29⟩
  · exact ⟨0x00000000f962313135c2dd29bfa264ae8b0226dffe508dd92c928d0149f10f80#256,
      (0xd37e597d#32, 0x94cf3cb3#32), by simpa [oneHotDifference] using cell_00_30⟩
  · exact ⟨0x00000000f0c47787e4d2ae5a1e8159ce8744eaa0fbdfdb7579410d2b2347a025#256,
      (0x775d8243#32, 0x8f93dc7f#32), by simpa [oneHotDifference] using cell_00_31⟩

end Magma.DiffanNineRoundPositiveRows
