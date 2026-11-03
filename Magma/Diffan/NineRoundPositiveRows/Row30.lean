module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row30Group00
public import Magma.Diffan.NineRoundPositiveRows.Row30Group01
public import Magma.Diffan.NineRoundPositiveRows.Row30Group02
public import Magma.Diffan.NineRoundPositiveRows.Row30Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 30. -/
theorem row30 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (30 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000006000b000b78fd2e2021118fd6b88e1b7e8066eb77e366bdb40bf3cbf#256,
      (0xb92d559a#32, 0xa52e820c#32), by simpa [oneHotDifference] using cell_30_00⟩
  · exact ⟨0x00000000be0100005ed06578572dcc95822085c3ba5cade0d6c103515db1d26a#256,
      (0x9d507b02#32, 0x56270490#32), by simpa [oneHotDifference] using cell_30_01⟩
  · exact ⟨0x000000005800008039de328e7497ec34be6240354b8334a215e759d095522e33#256,
      (0x62115e71#32, 0xed00d83c#32), by simpa [oneHotDifference] using cell_30_02⟩
  · exact ⟨0x000000002042effbe12a495c00b230d5916d058cb0d5ec6cc517992b08728901#256,
      (0xad4e598a#32, 0x2663bce1#32), by simpa [oneHotDifference] using cell_30_03⟩
  · exact ⟨0x000000009800a000a779edf074eb043b754abe84df38dfb779b793899f89daa8#256,
      (0xd3482ed4#32, 0x8ce5a994#32), by simpa [oneHotDifference] using cell_30_04⟩
  · exact ⟨0x00000000d000000032a454f891ddc19df45bfcf4f3a40e9ddf7ef40e129acfe0#256,
      (0x688ee81f#32, 0xbe789e72#32), by simpa [oneHotDifference] using cell_30_05⟩
  · exact ⟨0x000000002000c000d0f3059e814b2b9695b2bae0591b901784965842f206ff30#256,
      (0x9567561b#32, 0x05aa379c#32), by simpa [oneHotDifference] using cell_30_06⟩
  · exact ⟨0x000000005800000090c3669ce0e504c0a83e9eae09780adcea8a9fe039e67160#256,
      (0x13dd30e1#32, 0x1f99f12f#32), by simpa [oneHotDifference] using cell_30_07⟩
  · exact ⟨0x000000005a5647fea23eaaa839ba14ae0ab7d47e7e147f3cecd03b463199548e#256,
      (0x00814947#32, 0x192fa9ae#32), by simpa [oneHotDifference] using cell_30_08⟩
  · exact ⟨0x00000000e0003c00e1671f4198f6b5f3e9da4018079cd6e5dbf94a094282ab04#256,
      (0x28ffb059#32, 0xd8b1c158#32), by simpa [oneHotDifference] using cell_30_09⟩
  · exact ⟨0x000000007000000070d385421b5cdefdafd877cadf60a3b5dd3609085405db00#256,
      (0x78098411#32, 0xfcf23ba2#32), by simpa [oneHotDifference] using cell_30_10⟩
  · exact ⟨0x000000003c30ffff432b0c1d818212df6ef0bdd72c320d0fc5313e29090e0a00#256,
      (0xf84ee900#32, 0x82f7fad0#32), by simpa [oneHotDifference] using cell_30_11⟩
  · exact ⟨0x000000007000000033e7611bf17782b31ebd51e3f02954ad8972b8c7834d1008#256,
      (0x61d2b0aa#32, 0x2578d0bb#32), by simpa [oneHotDifference] using cell_30_12⟩
  · exact ⟨0x00000000d0000000ff5604797d5d06f49e08b6a958e0027d039bb443876b1000#256,
      (0x1f86f8e9#32, 0x4a5a1cec#32), by simpa [oneHotDifference] using cell_30_13⟩
  · exact ⟨0x000000009c0000003a19ec1f2bf85d3e6910d4658aff5ea7e2275bde958ac000#256,
      (0x2d2f56ae#32, 0xdf393b34#32), by simpa [oneHotDifference] using cell_30_14⟩
  · exact ⟨0x00000000c0ffc0002f8552458da7bc23492788a1e62d0f6efcf14987c0d3f050#256,
      (0x5bca9480#32, 0x0669d1d4#32), by simpa [oneHotDifference] using cell_30_15⟩
  · exact ⟨0x0000000038f800003ac6e5886f389c9948bf145913960485f8f24dcd52f30da0#256,
      (0x2e36413a#32, 0xba83d125#32), by simpa [oneHotDifference] using cell_30_16⟩
  · exact ⟨0x00000000f0000000a3d89c25424c1b6ca48088b254285352b70ded23ea518080#256,
      (0xb1415026#32, 0x4c4b8a49#32), by simpa [oneHotDifference] using cell_30_17⟩
  · exact ⟨0x00000000d000a0003019195e47fffaabb4c7f93ac6a7817c6f4d45ee1f8bf800#256,
      (0x51293419#32, 0x65fbc683#32), by simpa [oneHotDifference] using cell_30_18⟩
  · exact ⟨0x0000000098000000661060d486a330c6b4ba2e43cabed79ca6ac592ae0670000#256,
      (0x2c979643#32, 0xba53f1d2#32), by simpa [oneHotDifference] using cell_30_19⟩
  · exact ⟨0x00000000d0000000b9a155be59894b4c8fb7c9c3cbdd528c2da553df200f60a0#256,
      (0x2edd9c89#32, 0xed43b33a#32), by simpa [oneHotDifference] using cell_30_20⟩
  · exact ⟨0x000000006000e000e7e39cb7766751dae59f4e075f046cc0e1214738a8580000#256,
      (0x53195ab1#32, 0x573155ee#32), by simpa [oneHotDifference] using cell_30_21⟩
  · exact ⟨0x0000000040000000237c4d1a388bb328e49ad4c0b4d6766cf569e2fb40100004#256,
      (0xcc9cde56#32, 0xbc7a0ee6#32), by simpa [oneHotDifference] using cell_30_22⟩
  · exact ⟨0x0000000090ffe00062e10ea4b3228171e662be1beff35b6d19158e556b5fe033#256,
      (0xe3704d73#32, 0x8b70af0a#32), by simpa [oneHotDifference] using cell_30_23⟩
  · exact ⟨0x0000000050fd0000b5a13f4d57c0b4eed5f246bafb7480271222e3a9a88647f0#256,
      (0x50a5df98#32, 0x3593d373#32), by simpa [oneHotDifference] using cell_30_24⟩
  · exact ⟨0x000000007dfb00002a5ada1f6efde00fbeb0c2a90de28c9405f6624f00040900#256,
      (0xe2222399#32, 0x4b8223a5#32), by simpa [oneHotDifference] using cell_30_25⟩
  · exact ⟨0x00000000d0009000222beaefa98b10c7ead6d03915d0261ede11a3ffeb180080#256,
      (0x0868a24f#32, 0xb15de89d#32), by simpa [oneHotDifference] using cell_30_26⟩
  · exact ⟨0x00000000b800000040bcf3003d88ef66207b1faabab87cc7c493ec6b9d8b6500#256,
      (0x49b5ab5a#32, 0xfbfe6170#32), by simpa [oneHotDifference] using cell_30_27⟩
  · exact ⟨0x00000000b8000000b3841d00f9e4861482fb9125f5d7f2facba00527400000b0#256,
      (0xc5592272#32, 0xd01a335b#32), by simpa [oneHotDifference] using cell_30_28⟩
  · exact ⟨0x0000000060000000d889fce0134d03f389a2900452480a02cbbab2ca30000000#256,
      (0x4e5b3397#32, 0x641c2721#32), by simpa [oneHotDifference] using cell_30_29⟩
  · exact ⟨0x00000000100000008f606f63803a81c6067a649efd762d9ba993615c40650000#256,
      (0x52c8c48d#32, 0x25ba3e0a#32), by simpa [oneHotDifference] using cell_30_30⟩
  · exact ⟨0x00000000e00000004c464afdd3fb480b45aba072ff65e13155597090f86ebd69#256,
      (0x81e9e005#32, 0xda6c8dbc#32), by simpa [oneHotDifference] using cell_30_31⟩

end Magma.DiffanNineRoundPositiveRows
