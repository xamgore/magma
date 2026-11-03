module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row07Group00
public import Magma.Diffan.NineRoundPositiveRows.Row07Group01
public import Magma.Diffan.NineRoundPositiveRows.Row07Group02
public import Magma.Diffan.NineRoundPositiveRows.Row07Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 7. -/
theorem row07 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (7 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000008b712fbf44be3e6d605760d10fdb14528a0d0fc4bc8b19aad0359ac7#256,
      (0x137b1ae1#32, 0x874038c7#32), by simpa [oneHotDifference] using cell_07_00⟩
  · exact ⟨0x0000000029483a3fb34850862cd33f012fe94c93ee715ab61b6b51600ed9a351#256,
      (0xa49a1730#32, 0x504492c4#32), by simpa [oneHotDifference] using cell_07_01⟩
  · exact ⟨0x0000000093f5dc89f081c8f3213f05841bac9b0a7a137ab183605793a925aa3b#256,
      (0xea5652ce#32, 0x72bf7018#32), by simpa [oneHotDifference] using cell_07_02⟩
  · exact ⟨0x000000007b8d13c7ac5c2d0c3367b17395759a35050083446194bf821e553a69#256,
      (0x91d74972#32, 0xe13ebbc1#32), by simpa [oneHotDifference] using cell_07_03⟩
  · exact ⟨0x0000000055afab3d885edf82c6fb483c2074592b41f48c33134607032c4e4696#256,
      (0x2f19db81#32, 0x28fbad3f#32), by simpa [oneHotDifference] using cell_07_04⟩
  · exact ⟨0x00000000d3dc0d6f99b7a7df0773eeca68016b4798038c171238b8fbaefcf0ef#256,
      (0x74f3a628#32, 0xcf425ce4#32), by simpa [oneHotDifference] using cell_07_05⟩
  · exact ⟨0x000000008ab97a91257fffd554b83663f5d437f0e7f531f9ba9114177b8e099f#256,
      (0x90d4f590#32, 0x05c044a8#32), by simpa [oneHotDifference] using cell_07_06⟩
  · exact ⟨0x000000003bdab77fae1c5eb5780ae58d1ca55655017c7d4fd552010496fef7bc#256,
      (0x781f61fd#32, 0xfe885aa5#32), by simpa [oneHotDifference] using cell_07_07⟩
  · exact ⟨0x00000000781d64af7254f64fad90643f34176b42295e2bdec4141a0d8ae7bafe#256,
      (0xdca5055b#32, 0x3d4773fd#32), by simpa [oneHotDifference] using cell_07_08⟩
  · exact ⟨0x000000004164a0d2ec9742a21ba345d3bb3e4e7f340545fee09ea1b5b4454dc0#256,
      (0x96f3d711#32, 0x04def18f#32), by simpa [oneHotDifference] using cell_07_09⟩
  · exact ⟨0x00000000b8b1e57b838009868a9b86971d189c260dcc388208ae352e27600602#256,
      (0x562efb45#32, 0x73d87c80#32), by simpa [oneHotDifference] using cell_07_10⟩
  · exact ⟨0x00000000c22f4e9cebe15ca4085c9da2d90884ca22b2c5e16e1019ca778124cc#256,
      (0x41c7deed#32, 0x2c10149a#32), by simpa [oneHotDifference] using cell_07_11⟩
  · exact ⟨0x00000000868a308f180036153ea03f71c4bc410ea450041a7e8c3e79e710d182#256,
      (0x5b22b6bd#32, 0x7c67649e#32), by simpa [oneHotDifference] using cell_07_12⟩
  · exact ⟨0x0000000042c59eabe9934d8a3d6ef035e06120580aa51d3c134c4c107dcc602c#256,
      (0x24fa0436#32, 0xab1aeee0#32), by simpa [oneHotDifference] using cell_07_13⟩
  · exact ⟨0x000000005efd4c430435f346f9937a4978e082f895e906c1682b3f3e55d26116#256,
      (0x28beb5b8#32, 0x3133191c#32), by simpa [oneHotDifference] using cell_07_14⟩
  · exact ⟨0x0000000036b39730c99386ae35bda8dee33a41f556e5699b19286a47537cf01f#256,
      (0xe6b85b65#32, 0x1487de12#32), by simpa [oneHotDifference] using cell_07_15⟩
  · exact ⟨0x000000002882b39145e1d33100ba0092756d7b69e0a941da1b6204d835e79a00#256,
      (0x3ebc34dc#32, 0x4456e32e#32), by simpa [oneHotDifference] using cell_07_16⟩
  · exact ⟨0x0000000056e7695f36641d05987d7670179d95ebaeb4ecdb288d72f1223e0ffe#256,
      (0x2dbdf3b4#32, 0xae1b2350#32), by simpa [oneHotDifference] using cell_07_17⟩
  · exact ⟨0x0000000053fc0f8fcafb9fc1c34c2d19ca74bfe740c79c55d25284419d49fcf8#256,
      (0xadffb2ba#32, 0x58dbc519#32), by simpa [oneHotDifference] using cell_07_18⟩
  · exact ⟨0x000000008ff85747b873b88b8576e5ac9e80e69aec63c7d9cb2b101d7a26f28a#256,
      (0xc0014d54#32, 0xe4c22ed0#32), by simpa [oneHotDifference] using cell_07_19⟩
  · exact ⟨0x0000000097ec50afe3ad8472ff9c0ad3f648595290973938fb694fca9131853c#256,
      (0xb6d4a023#32, 0x2430439f#32), by simpa [oneHotDifference] using cell_07_20⟩
  · exact ⟨0x000000000da311386d036b5de02625b2a771719fd53aeda361ebfabc30000000#256,
      (0x49befa57#32, 0x6e198ca3#32), by simpa [oneHotDifference] using cell_07_21⟩
  · exact ⟨0x00000000e92bd66fbdd393b61b864d3e5831fbb4e6b352b71db8479ca66fc61c#256,
      (0x6663f471#32, 0xabe44ef6#32), by simpa [oneHotDifference] using cell_07_22⟩
  · exact ⟨0x000000001542b0b82f139cad22408b97d8775ef62479831f20ce32bed6902e58#256,
      (0x99b25a3d#32, 0xebcba993#32), by simpa [oneHotDifference] using cell_07_23⟩
  · exact ⟨0x00000000c47f6ee2e946c07ecff9f3073de668fd8d5f6936989f151db3847809#256,
      (0x176db15e#32, 0x4d72e751#32), by simpa [oneHotDifference] using cell_07_24⟩
  · exact ⟨0x00000000bd25e58c9f9559e50868a7e101acb6e4616e0df1fbff462b71a4c000#256,
      (0xf4584189#32, 0x1d634fa6#32), by simpa [oneHotDifference] using cell_07_25⟩
  · exact ⟨0x00000000b9c4a91f16dcfc7fc923420c1c3204f60f9dbbe5669eb782b3d6e009#256,
      (0x1c905983#32, 0x2709b20f#32), by simpa [oneHotDifference] using cell_07_26⟩
  · exact ⟨0x000000003c80c92f07981e499d14b3f3441918aff4188a0e6d92061e843a0b00#256,
      (0x2421e3eb#32, 0xab28d0d4#32), by simpa [oneHotDifference] using cell_07_27⟩
  · exact ⟨0x00000000b6a77a9f657f0bd091d463c145a0fba58bec08c4b9acfa0aeffffff8#256,
      (0x95ab9a1d#32, 0x9967e80d#32), by simpa [oneHotDifference] using cell_07_28⟩
  · exact ⟨0x00000000517f08b9f97c927e32ff162116110006dab80ab9d309d37c01ff8fff#256,
      (0x611dc3ed#32, 0xca316152#32), by simpa [oneHotDifference] using cell_07_29⟩
  · exact ⟨0x00000000d913ce9c917a8169a67d13038b5f77eacbb8ef46dcf36221f2c7010c#256,
      (0x01f86f6f#32, 0xdfa60316#32), by simpa [oneHotDifference] using cell_07_30⟩
  · exact ⟨0x00000000c29a0bdfb7e53b140d67c418895b93e5ae1297b64f0fcbddfea75e20#256,
      (0x106872c7#32, 0x30db09cc#32), by simpa [oneHotDifference] using cell_07_31⟩

end Magma.DiffanNineRoundPositiveRows
