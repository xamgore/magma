module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row31Group00
public import Magma.Diffan.NineRoundPositiveRows.Row31Group01
public import Magma.Diffan.NineRoundPositiveRows.Row31Group02
public import Magma.Diffan.NineRoundPositiveRows.Row31Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 31. -/
theorem row31 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (31 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000f874a9a6422a0c708d41ee0e99176af8cb2708f6717bfe6d8f7eb87d#256,
      (0xffde7c2e#32, 0x8049915f#32), by simpa [oneHotDifference] using cell_31_00⟩
  · exact ⟨0x00000000f7682b725efa334baa2902a69c9f24d7fe4961f0512936c0804e0b5b#256,
      (0x4c81f06b#32, 0x972a3691#32), by simpa [oneHotDifference] using cell_31_01⟩
  · exact ⟨0x00000000730b59ef9b103c5380c910002f44d8f4a44681995e8ceb09248dc897#256,
      (0xbd81ccfa#32, 0x51687f2a#32), by simpa [oneHotDifference] using cell_31_02⟩
  · exact ⟨0x000000000b9886a9874566f800ae3c022a45799b38a238d4816ae735f13527b9#256,
      (0x82e0a748#32, 0x632b49ab#32), by simpa [oneHotDifference] using cell_31_03⟩
  · exact ⟨0x000000009fec830f953f3a7b2d8a8e9c05d72c0edff6d648a77993dfdc8706b0#256,
      (0xfebd4cf5#32, 0x8e5f7c38#32), by simpa [oneHotDifference] using cell_31_04⟩
  · exact ⟨0x00000000258e79f29fac418bc5c41b37abf52da5e54d4f0fd354c08580f21c75#256,
      (0x648a4046#32, 0xe66855bd#32), by simpa [oneHotDifference] using cell_31_05⟩
  · exact ⟨0x00000000f6609d04fca74e2f08d5760a8ff8b1f0183f3f3f3bdac123b8c54c8f#256,
      (0xd85733b4#32, 0xf5174fea#32), by simpa [oneHotDifference] using cell_31_06⟩
  · exact ⟨0x00000000dfe65e6cd8afa986fac70ea5d2bcebca70098c08c037653056d089c0#256,
      (0x1a885551#32, 0x317c3038#32), by simpa [oneHotDifference] using cell_31_07⟩
  · exact ⟨0x000000003a16eb64cb854cb086b5b1bc8be8e9633d9c8df1cf1814434feabd00#256,
      (0x5420de15#32, 0x05d6542f#32), by simpa [oneHotDifference] using cell_31_08⟩
  · exact ⟨0x00000000ee9b83ecf21875133ed7f8b4cf1573ba528fda55237eaaaf983801cf#256,
      (0x9806a724#32, 0xcd61762d#32), by simpa [oneHotDifference] using cell_31_09⟩
  · exact ⟨0x00000000380f6ef34af0caa088ccdb966363ea2382e0640cb0563ab548266d00#256,
      (0x25e4e74c#32, 0xddd351c2#32), by simpa [oneHotDifference] using cell_31_10⟩
  · exact ⟨0x00000000f69566907c5e8440225901c7fe554a88a794be4288bb4e1c313b3cd0#256,
      (0xd9d0988b#32, 0xc01fe23b#32), by simpa [oneHotDifference] using cell_31_11⟩
  · exact ⟨0x00000000f789a9a5b4f805b548bbeccd1af5666d0e0d8d2d6b5c043d1fd9c800#256,
      (0x5f1c3ef2#32, 0x8d332156#32), by simpa [oneHotDifference] using cell_31_12⟩
  · exact ⟨0x000000007305e00b824bff80f9690ef2f189243cca6c4353bbd953394322d000#256,
      (0xe043f935#32, 0xf03ca336#32), by simpa [oneHotDifference] using cell_31_13⟩
  · exact ⟨0x00000000d63d7b4bb87c71a852ec1a111d13144ecb504b0bd61c1e18b95e4000#256,
      (0xbea47cc0#32, 0x465fdc0b#32), by simpa [oneHotDifference] using cell_31_14⟩
  · exact ⟨0x00000000e0cc6b548704e467a93c9afe1d428f76830643f2e4223f422cd9b800#256,
      (0x22fff6c8#32, 0x89a7ff19#32), by simpa [oneHotDifference] using cell_31_15⟩
  · exact ⟨0x00000000f7e368c908d406e085943d6e4d7d7dd275c86a1701939b36bdb4c000#256,
      (0x6607b4ec#32, 0xce371b0f#32), by simpa [oneHotDifference] using cell_31_16⟩
  · exact ⟨0x0000000066a8daed77cb8283f45412a09235762f2da5931152713ce1db06be08#256,
      (0xd6fe94c4#32, 0x95cbc77d#32), by simpa [oneHotDifference] using cell_31_17⟩
  · exact ⟨0x000000008e55337849bd2ef051ae359e668018487675b22603a6eef4f1c20000#256,
      (0xe34ada17#32, 0xc6eeb224#32), by simpa [oneHotDifference] using cell_31_18⟩
  · exact ⟨0x0000000096db77796cacc70e84d6847232c7cca9b1f747e44a1c2e6836a7800d#256,
      (0x8e9a5509#32, 0xc2cf689d#32), by simpa [oneHotDifference] using cell_31_19⟩
  · exact ⟨0x00000000a5fdb640f04d62fb681acb38509c957bf09c2541017f8c2a53b00008#256,
      (0x27eb0cda#32, 0xaec1fc2e#32), by simpa [oneHotDifference] using cell_31_20⟩
  · exact ⟨0x000000004521013eb90593dbc026de0b08152b74636a67c1915998e993200000#256,
      (0xa6b49ca3#32, 0xe7528b76#32), by simpa [oneHotDifference] using cell_31_21⟩
  · exact ⟨0x00000000fba4395b7fba02789b773adf27a7e7c06c4714e40384bcf8d7500000#256,
      (0xf5140481#32, 0xf9469dd4#32), by simpa [oneHotDifference] using cell_31_22⟩
  · exact ⟨0x0000000035dc8af219a985570f9466364fd2e6699b2dc3f49f3295ab2690001b#256,
      (0x135d7927#32, 0xdb7a28da#32), by simpa [oneHotDifference] using cell_31_23⟩
  · exact ⟨0x00000000ccb00867838559aa6f7d41a8952e239c94003eb06d54549bc8e80080#256,
      (0xb25201f7#32, 0xfa66c59a#32), by simpa [oneHotDifference] using cell_31_24⟩
  · exact ⟨0x00000000bc60af368c1de54567a45cb880853f176a7c1629c1cc788e9b001000#256,
      (0x89d98859#32, 0xf23afbfd#32), by simpa [oneHotDifference] using cell_31_25⟩
  · exact ⟨0x0000000036f8abdc1a52beb99d70597cf7ee5d62232850a54b3dcd2771000000#256,
      (0x801fa241#32, 0xd1812684#32), by simpa [oneHotDifference] using cell_31_26⟩
  · exact ⟨0x00000000e6a9f6c43e32cbcd76cda51c37f75700b7e529dc4fdb78f013800003#256,
      (0xb5cb670b#32, 0xd01113c5#32), by simpa [oneHotDifference] using cell_31_27⟩
  · exact ⟨0x00000000fada3d5fe4d454a011f003eb9b97c8fd2dfef64219300df4af000000#256,
      (0x5cb48b53#32, 0x77c7cc7a#32), by simpa [oneHotDifference] using cell_31_28⟩
  · exact ⟨0x00000000cd81e1b8fdbb073091192b79f7027f5c52e95f241d0aa20470003000#256,
      (0x62b743e6#32, 0x1f689e90#32), by simpa [oneHotDifference] using cell_31_29⟩
  · exact ⟨0x000000003102880416c12ab901ebce9de4ef9a6bd5efcb7d595a2c0250002801#256,
      (0xe278897f#32, 0xf1caf32b#32), by simpa [oneHotDifference] using cell_31_30⟩
  · exact ⟨0x0000000049e14a798fe6b43085b79d9e25d84f409b37bcc2a264c1b021e467d4#256,
      (0xda3ca607#32, 0x74f0ab8c#32), by simpa [oneHotDifference] using cell_31_31⟩

end Magma.DiffanNineRoundPositiveRows
