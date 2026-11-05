module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row14Group00
public import Magma.Differential.NinePlus.PositiveRows.Row14Group01
public import Magma.Differential.NinePlus.PositiveRows.Row14Group02
public import Magma.Differential.NinePlus.PositiveRows.Row14Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 14. -/
theorem row14 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (14 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000bea643038760358b0589126cd9a639b98f4d990aa8676cb8d496178b#256,
      (0xdf9c578d#32, 0xf1d043cc#32), by simpa [oneHotDifference] using cell_14_00⟩
  · exact ⟨0x000000005a133c5cfd1d055da3e522eba7eea48bce7b92df96dfe12d061dcb15#256,
      (0x47bb4ce9#32, 0xb5c426fa#32), by simpa [oneHotDifference] using cell_14_01⟩
  · exact ⟨0x00000000f3554fff3f32fbff79b60d90f75a74d3b8e8727ff47fcbef5bafe98c#256,
      (0xac0db86d#32, 0x49833b90#32), by simpa [oneHotDifference] using cell_14_02⟩
  · exact ⟨0x00000000bf355fffe5f81252c5d2b94c8499e2828b64c645e7174bd543ed1eda#256,
      (0xcc0e19fe#32, 0xd610b346#32), by simpa [oneHotDifference] using cell_14_03⟩
  · exact ⟨0x00000000e3232fff4e00edb535b807be332accca4ac5d7da0fbb40f1106639f3#256,
      (0x9b7f74a6#32, 0x643febb1#32), by simpa [oneHotDifference] using cell_14_04⟩
  · exact ⟨0x0000000042c0c0ff8ce49b3c6b5ad0897bcb09f3a927d9bec3b66883f0b7e7a0#256,
      (0xaaf744af#32, 0x892e6dea#32), by simpa [oneHotDifference] using cell_14_05⟩
  · exact ⟨0x0000000000f2cbfa1fe36835398a7e3728f7735baa525f49863879ccb9a900f0#256,
      (0x6e4ba5c3#32, 0x731353d8#32), by simpa [oneHotDifference] using cell_14_06⟩
  · exact ⟨0x00000000b7493e403737d41111c8548ba7d8b8723d5dd799a360633f14caf3d2#256,
      (0xac66744e#32, 0x7f58e688#32), by simpa [oneHotDifference] using cell_14_07⟩
  · exact ⟨0x000000002fb650ffb58b7fadc7159fc0b45187c655362150a8513b3b80fdbf48#256,
      (0xfadb6292#32, 0x72d4e462#32), by simpa [oneHotDifference] using cell_14_08⟩
  · exact ⟨0x0000000002becfffe4b5d71f7a1cebf7503e01ff1821dd5c119f1e6c87ac79fc#256,
      (0x6e38d717#32, 0x0f98153e#32), by simpa [oneHotDifference] using cell_14_09⟩
  · exact ⟨0x0000000022afc29258a4bf8259002cf21e6129a6655f6e65cad351d759edcdfc#256,
      (0xbb070f58#32, 0x8488cae9#32), by simpa [oneHotDifference] using cell_14_10⟩
  · exact ⟨0x00000000427347fc9dd26fe37e331293bd9f29aa40d2f520dc7ecd75482e1b09#256,
      (0xf13a48d1#32, 0x93308ed3#32), by simpa [oneHotDifference] using cell_14_11⟩
  · exact ⟨0x000000009ccf0fff9680a9348acda5940331580a5bec3ba867c49d398050d004#256,
      (0xa3f9d9fa#32, 0x0550272a#32), by simpa [oneHotDifference] using cell_14_12⟩
  · exact ⟨0x000000005160cfffeb0089302dbf6b0494291f33b0e527ec20d0749696442fff#256,
      (0x6e33e1bd#32, 0x0e74b24c#32), by simpa [oneHotDifference] using cell_14_13⟩
  · exact ⟨0x000000001b55afff331a8599eb044234fe9ea23c774d6f3b7a5529074dcd4ff6#256,
      (0x71ebb190#32, 0x1dbfa33f#32), by simpa [oneHotDifference] using cell_14_14⟩
  · exact ⟨0x000000005c329000783bf8f621bf90ee4c555acd28d1b02c9f315ede36b37f00#256,
      (0x531f3cef#32, 0xcb1b36ac#32), by simpa [oneHotDifference] using cell_14_15⟩
  · exact ⟨0x00000000020f9fff228921c80b8a4d1a3c462514640ff90c09c457b89d98efc0#256,
      (0x6392f40e#32, 0xb34c0c67#32), by simpa [oneHotDifference] using cell_14_16⟩
  · exact ⟨0x0000000023a45762701306a4980a202033a6244880d7e2e1a4729ec8db7d0085#256,
      (0x50e0bbae#32, 0xb4ae8a00#32), by simpa [oneHotDifference] using cell_14_17⟩
  · exact ⟨0x000000001531dfff6fcf9a32e891dc401b4d187ff20de7df96d7d132ce8afff3#256,
      (0x3c29400c#32, 0x4e344c99#32), by simpa [oneHotDifference] using cell_14_18⟩
  · exact ⟨0x00000000891eb3ee12c5e3e480dd7b4818bedd4b03221c9bd35d824490a3fd3b#256,
      (0x95763fec#32, 0xb84b8492#32), by simpa [oneHotDifference] using cell_14_19⟩
  · exact ⟨0x0000000002896000e4168ba33abab7cca0a7be51069186d151e0fc0333908000#256,
      (0xbfe9ecf6#32, 0xf493b19a#32), by simpa [oneHotDifference] using cell_14_20⟩
  · exact ⟨0x00000000509de0a67a5fc00bbce9fd50a660f6091902a72cbe49fb86ff473ccd#256,
      (0xd707803c#32, 0x277fd6c6#32), by simpa [oneHotDifference] using cell_14_21⟩
  · exact ⟨0x00000000ee2a380014e6f48c34e5f6b7666b61a03f96cbd6ba3bf41541400000#256,
      (0x3233b177#32, 0x821b8c76#32), by simpa [oneHotDifference] using cell_14_22⟩
  · exact ⟨0x0000000047d83fffb6ea3747a47a228d4e7ada0b66aba7fa801b2132d75d301f#256,
      (0x8226d87c#32, 0x8c89af2e#32), by simpa [oneHotDifference] using cell_14_23⟩
  · exact ⟨0x0000000045ae900091e2889315e39e6fbc7e052cd9e9db441466e4521c088008#256,
      (0xe29f319a#32, 0x18273d7c#32), by simpa [oneHotDifference] using cell_14_24⟩
  · exact ⟨0x00000000219930c5b7c02454a7ef6d6ddb86fa20c205270f217cdc1650ed8f80#256,
      (0x51c9b844#32, 0xb10c629a#32), by simpa [oneHotDifference] using cell_14_25⟩
  · exact ⟨0x00000000a97a34c03b38e3255b91809e7fcbe2a2e9ade4cd53c9b13c0e366000#256,
      (0x2dbf99d0#32, 0x03122aac#32), by simpa [oneHotDifference] using cell_14_26⟩
  · exact ⟨0x0000000010f8afffccbb351dbc86606fbe806b17c298c035a736c419b27c0030#256,
      (0x8effe04c#32, 0xa2eda188#32), by simpa [oneHotDifference] using cell_14_27⟩
  · exact ⟨0x000000006223b000cfcee20112ed9d1e9ed6bc40466ccbccfd07da8500108000#256,
      (0xd518fb0c#32, 0x8a32334a#32), by simpa [oneHotDifference] using cell_14_28⟩
  · exact ⟨0x00000000a22943ff231deb61e8c0282998f5ed5d784c0abd3386398680e07c00#256,
      (0xf50034c4#32, 0xa96a36da#32), by simpa [oneHotDifference] using cell_14_29⟩
  · exact ⟨0x00000000f5039fff21c76a95e9b5bc365dade5103e447ce3afb45dec2104d03c#256,
      (0x973fda91#32, 0xed9363be#32), by simpa [oneHotDifference] using cell_14_30⟩
  · exact ⟨0x0000000006182000df86a9de14834f8b66cb72fbe691bf259e8665704f25e377#256,
      (0x57d2286d#32, 0xc0332ecf#32), by simpa [oneHotDifference] using cell_14_31⟩

end Magma.DifanNineRoundPositiveRows
