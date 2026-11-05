module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row11Group00
public import Magma.Differential.NinePlus.PositiveRows.Row11Group01
public import Magma.Differential.NinePlus.PositiveRows.Row11Group02
public import Magma.Differential.NinePlus.PositiveRows.Row11Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 11. -/
theorem row11 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (11 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000008ccae900141b207bf0d104f45fa729e609a8da13bd19f581b6c9e29b#256,
      (0x96251d8f#32, 0x194da4ec#32), by simpa [oneHotDifference] using cell_11_00⟩
  · exact ⟨0x000000005a5fc4f8ddf2f82bacc784f3e118197beb52b8c308590a110976bcee#256,
      (0xbff78157#32, 0x535bd6fb#32), by simpa [oneHotDifference] using cell_11_01⟩
  · exact ⟨0x000000003021d7ffc7981fd73fa3090ebcbd5f24f6fd1b347477533d1fd81c9e#256,
      (0x53dd0bf4#32, 0xc01a2f05#32), by simpa [oneHotDifference] using cell_11_02⟩
  · exact ⟨0x000000009a660c78c726be7d5b0acbf465e2d60be7f2143e19a6e29d411cefa6#256,
      (0xadc7ef4e#32, 0x61b1907d#32), by simpa [oneHotDifference] using cell_11_03⟩
  · exact ⟨0x000000002cfe9dff207b6e0cd7797a02ef75d6124827c416287e700593e93bef#256,
      (0x8cc8ff9d#32, 0x30d9413d#32), by simpa [oneHotDifference] using cell_11_04⟩
  · exact ⟨0x0000000074de19fb92b78d88a1b4ff4ec9f8f918b80507b08118f4f5b107ce18#256,
      (0x59aca58e#32, 0x00c3b959#32), by simpa [oneHotDifference] using cell_11_05⟩
  · exact ⟨0x000000008c3f22fe3e149692010cb436d943302080eedd58cb9ad1f4b5152b9b#256,
      (0x7c3c47be#32, 0x5168654d#32), by simpa [oneHotDifference] using cell_11_06⟩
  · exact ⟨0x00000000fd2767ff00244ceff46dbb83456e8039065610328d0145395710d4d0#256,
      (0x70c4e074#32, 0x34d4511e#32), by simpa [oneHotDifference] using cell_11_07⟩
  · exact ⟨0x0000000055298c7ce73e54cff992119f44a210c7c852028cee1ade37fa429f00#256,
      (0x4e731d91#32, 0x2b104b5a#32), by simpa [oneHotDifference] using cell_11_08⟩
  · exact ⟨0x000000001f49f6ff7840d97fb0523ead6b9322fbe05d1a646f7337e52f235acf#256,
      (0xdb6b1a2e#32, 0xbb4db05d#32), by simpa [oneHotDifference] using cell_11_09⟩
  · exact ⟨0x00000000d6429bff8a993ca65b66b39e69e805ed69d8f96d0f40a0fa8290a507#256,
      (0xc9fec22d#32, 0xf64c53b1#32), by simpa [oneHotDifference] using cell_11_10⟩
  · exact ⟨0x000000003a7619fff11e6e750ac2c7cbe25b2cde5ee05d21a6b418b4549d6b0f#256,
      (0x648e4bed#32, 0xf75f2ff5#32), by simpa [oneHotDifference] using cell_11_11⟩
  · exact ⟨0x00000000f8212afe84403e610dafc17678112bddb885255a3987bca0751c87b0#256,
      (0xdf025747#32, 0xd929b94f#32), by simpa [oneHotDifference] using cell_11_12⟩
  · exact ⟨0x00000000c6e89a5d8d000f9067f1854371864c3005333f93c10a6ab68da05f30#256,
      (0x3ae73978#32, 0x6e0338e6#32), by simpa [oneHotDifference] using cell_11_13⟩
  · exact ⟨0x000000003bf4dcc04c45657de5986d17c9e8f64e69a025efa24ab5c1964ba3e0#256,
      (0x7baa1237#32, 0x4a126b2b#32), by simpa [oneHotDifference] using cell_11_14⟩
  · exact ⟨0x000000005068f7fcaf340c1604efc734007260216c17194e9e2dad839dd1a203#256,
      (0x7f261be4#32, 0x1c6d3e2d#32), by simpa [oneHotDifference] using cell_11_15⟩
  · exact ⟨0x00000000b0c21c7dda32cf54dcd6067b031ef5371a33dc94175f7ccf16431f59#256,
      (0x96b27652#32, 0xa441c9fd#32), by simpa [oneHotDifference] using cell_11_16⟩
  · exact ⟨0x00000000d4fc2f10abc0a81b145bcb90ba72ed5dbb2d8049103e1a74b455ebf7#256,
      (0x60f2de29#32, 0x35a3c82f#32), by simpa [oneHotDifference] using cell_11_17⟩
  · exact ⟨0x0000000073b62dc17e2d74d9bdcd1b426d3853307dfbf212ee3b28d805057600#256,
      (0x3b834a35#32, 0xba8e6d63#32), by simpa [oneHotDifference] using cell_11_18⟩
  · exact ⟨0x00000000770c880f4bd13d914c59be2fae24fac4b6cdaef39d05a1b3c49a91bd#256,
      (0x2bec654b#32, 0x53bb719d#32), by simpa [oneHotDifference] using cell_11_19⟩
  · exact ⟨0x000000000ce80eff0d831fee390b17e6148b96b0420f9d42ea628455913705c4#256,
      (0x739b68d4#32, 0x019bf9b6#32), by simpa [oneHotDifference] using cell_11_20⟩
  · exact ⟨0x00000000bbf43300e016ba0bb0b8728c31bac65b0f4ff694f57772623f500000#256,
      (0x1bae53ce#32, 0x3b876bc3#32), by simpa [oneHotDifference] using cell_11_21⟩
  · exact ⟨0x00000000647ed4ff1bbf77b678e8ebe70cdd2d2a1aa8f5b6437f6ad3aadfff80#256,
      (0xe6099205#32, 0x7921f98b#32), by simpa [oneHotDifference] using cell_11_22⟩
  · exact ⟨0x00000000668b06fc9ec3bd3ab99ee101eadcd558d41ca286dafa253e23973000#256,
      (0xd0c79221#32, 0xbfc7ce00#32), by simpa [oneHotDifference] using cell_11_23⟩
  · exact ⟨0x00000000aea219ffa7de12c490298cb608fd200144d1fe066b106b7184f6fffe#256,
      (0x6f26a521#32, 0x3cca0507#32), by simpa [oneHotDifference] using cell_11_24⟩
  · exact ⟨0x00000000fa9ad0dede3877dca74b23120882672be4d893a598766dc685ce3010#256,
      (0x93903406#32, 0x1723e353#32), by simpa [oneHotDifference] using cell_11_25⟩
  · exact ⟨0x000000005b8999002c423862d831f7ff2a925225788d2294a9f1b8e287000000#256,
      (0xb2980b98#32, 0xef6cd01a#32), by simpa [oneHotDifference] using cell_11_26⟩
  · exact ⟨0x00000000604d54ffd1cb30dbfa0bec5257b8192b4870683e37c4164ff9fffff0#256,
      (0xbc66a3f6#32, 0x4bcf6b1c#32), by simpa [oneHotDifference] using cell_11_27⟩
  · exact ⟨0x000000009bf5eeff02f97fc8560bbe3c1eb14544b41413f0d0498406efb90cff#256,
      (0x116cb52c#32, 0xe1c09cd5#32), by simpa [oneHotDifference] using cell_11_28⟩
  · exact ⟨0x000000006ba8b900acd65cfaea5a9fc3a178862d285e84853602b41bb0bef800#256,
      (0x5bd5b3c3#32, 0x818c6f6e#32), by simpa [oneHotDifference] using cell_11_29⟩
  · exact ⟨0x000000006e4408ff3806158dc54bb1483d5626fb85293b11e3ee1b3acfffc0f7#256,
      (0x4696ae90#32, 0x0c58d956#32), by simpa [oneHotDifference] using cell_11_30⟩
  · exact ⟨0x00000000cb8a95ff71161abc0c993a36bcdae651867799804879c22acc98faaa#256,
      (0xf8a00408#32, 0x42978b5a#32), by simpa [oneHotDifference] using cell_11_31⟩

end Magma.DiffanNineRoundPositiveRows
