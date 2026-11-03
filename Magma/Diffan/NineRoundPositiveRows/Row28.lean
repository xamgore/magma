module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row28Group00
public import Magma.Diffan.NineRoundPositiveRows.Row28Group01
public import Magma.Diffan.NineRoundPositiveRows.Row28Group02
public import Magma.Diffan.NineRoundPositiveRows.Row28Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 28. -/
theorem row28 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (28 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000080000007b079dc1fba95b835af17d255938e195251d052da12fe5e5#256,
      (0xb46c636a#32, 0xdfe54c3b#32), by simpa [oneHotDifference] using cell_28_00⟩
  · exact ⟨0x0000000050000000582c257c9a57034cbe1efcecbe93ee807e0f6eb7779c922b#256,
      (0xad13a40f#32, 0xe75ba621#32), by simpa [oneHotDifference] using cell_28_01⟩
  · exact ⟨0x00000000f00000006f28f27d09f67416159415c6118dbde71cbf8250e5a4e844#256,
      (0x1c39cf7f#32, 0x6c132c8f#32), by simpa [oneHotDifference] using cell_28_02⟩
  · exact ⟨0x00000000541e701cec7f3f2da69eacdacf85e93394016ff57cdc065073ca5507#256,
      (0xf83319ed#32, 0xd900ff94#32), by simpa [oneHotDifference] using cell_28_03⟩
  · exact ⟨0x00000000f08832007a7e51ae3c7cc30b6e0f14955fad54f855215b9dbd26faf0#256,
      (0x5caf8482#32, 0x244a730d#32), by simpa [oneHotDifference] using cell_28_04⟩
  · exact ⟨0x000000002e000000f2d32af00f4d518494467899eae7ee5ba819c29e7ee105b0#256,
      (0x15b7446f#32, 0x268e62b7#32), by simpa [oneHotDifference] using cell_28_05⟩
  · exact ⟨0x000000005003e000ab615aeb4a5a57e7c8cced1012a6be18e9d4967e7ef9be30#256,
      (0xd21f8c21#32, 0x25dc53f5#32), by simpa [oneHotDifference] using cell_28_06⟩
  · exact ⟨0x00000000ef8300006a4a95ba1401f44a6014f13d26bc9fa25e461dc04819ddf0#256,
      (0x81f04c5d#32, 0xf94b2a55#32), by simpa [oneHotDifference] using cell_28_07⟩
  · exact ⟨0x00000000c7b00000b364ab6ddddedb5c4d5e00eed9a8868b136ba5e5d53b6b00#256,
      (0x021d16ab#32, 0x72ead13f#32), by simpa [oneHotDifference] using cell_28_08⟩
  · exact ⟨0x00000000ee030000f7fb049f15655ad57cbec503be1c64624774aa5558e65dc0#256,
      (0xddbb40ab#32, 0xc2156470#32), by simpa [oneHotDifference] using cell_28_09⟩
  · exact ⟨0x0000000048020000ef9bd7549ce5c62f2958184edc120452a071f51044c2bd08#256,
      (0x713cc84c#32, 0x8fda0072#32), by simpa [oneHotDifference] using cell_28_10⟩
  · exact ⟨0x000000006f880000792fc359088a1073f42b0515fcdda772a7ce8fa2dd913f00#256,
      (0x6e297498#32, 0x21f04b65#32), by simpa [oneHotDifference] using cell_28_11⟩
  · exact ⟨0x00000000c0800000bb6786627a72cb455fdf07fc27c7337cabe324480f64b000#256,
      (0x663dca7a#32, 0x7ada6d47#32), by simpa [oneHotDifference] using cell_28_12⟩
  · exact ⟨0x0000000028000000c3ac7c8b0603588585f1d20660be19e6fe4f45bf3fbdb000#256,
      (0x2e7a11cf#32, 0xbb6e4247#32), by simpa [oneHotDifference] using cell_28_13⟩
  · exact ⟨0x0000000050000000578aed150978c4a7d1ff89d917e701ada5e400b88fb19000#256,
      (0xe609e87a#32, 0x6a943120#32), by simpa [oneHotDifference] using cell_28_14⟩
  · exact ⟨0x00000000f65fc0007d3a0b121a52fc20de84929dcec7280fe8429298e7185000#256,
      (0x6ba4d660#32, 0x99c8444d#32), by simpa [oneHotDifference] using cell_28_15⟩
  · exact ⟨0x00000000b803c0006e602bdf783f19ba6fe52bc6f6b300c2bd74cc2acd84d000#256,
      (0x19129125#32, 0xaf8ba7d8#32), by simpa [oneHotDifference] using cell_28_16⟩
  · exact ⟨0x00000000b1570000eb039eaceb6920dd93ae156b8fa3bd3dc5be95115d4f0000#256,
      (0xb26f1066#32, 0x3b3c4f73#32), by simpa [oneHotDifference] using cell_28_17⟩
  · exact ⟨0x00000000b080300074a04947e27bfda30e450f8a4a88e0e3d19525e7ce74fc00#256,
      (0x19e5abf8#32, 0x5cd39662#32), by simpa [oneHotDifference] using cell_28_18⟩
  · exact ⟨0x0000000048080000fef8d1ec0035405305570346bbdce280974543f0178a1d08#256,
      (0x2343a33d#32, 0x3749e9f5#32), by simpa [oneHotDifference] using cell_28_19⟩
  · exact ⟨0x00000000100800009091867c0c3105e1c47dfe68207fe34d8a81db171a700000#256,
      (0x994b4175#32, 0x81cd347f#32), by simpa [oneHotDifference] using cell_28_20⟩
  · exact ⟨0x00000000080000008a758bf1b76d24ea05edc34bbaca0a782254a45dfa1900f0#256,
      (0xe2b26a9d#32, 0xbd8786f8#32), by simpa [oneHotDifference] using cell_28_21⟩
  · exact ⟨0x0000000030000000d2adc3a3ba6e9019469f9815166ede7bc5719031ff97c000#256,
      (0x5a71bc8d#32, 0x5de75488#32), by simpa [oneHotDifference] using cell_28_22⟩
  · exact ⟨0x00000000cc0400001c08e510f8496799117a0923eda537bfb069dd5f3a462ea0#256,
      (0x82999bba#32, 0xe143e2d4#32), by simpa [oneHotDifference] using cell_28_23⟩
  · exact ⟨0x000000008ffe00005653ddb2841740c4cd7e34d7f087871d203384cf92eef000#256,
      (0x63b2fe92#32, 0xfbc346ea#32), by simpa [oneHotDifference] using cell_28_24⟩
  · exact ⟨0x00000000b0800000de0552be38cdc6474c09cbfe8ab7759c68936af5818f8000#256,
      (0x78fa593e#32, 0x91cf2ad9#32), by simpa [oneHotDifference] using cell_28_25⟩
  · exact ⟨0x00000000e00f8000cad9c370bb911fc927f081c32fa35ef6619989d3caa00009#256,
      (0xe0248e52#32, 0x5dd6aaad#32), by simpa [oneHotDifference] using cell_28_26⟩
  · exact ⟨0x0000000038000000e308486b3a257de2c1a5d96634ff538a1eaf3cad87000000#256,
      (0xcfcd6693#32, 0x799e55b9#32), by simpa [oneHotDifference] using cell_28_27⟩
  · exact ⟨0x000000006008300030a4d4c8ac60baa939b5e5d6270631975f641d7a5000fc00#256,
      (0x3f442121#32, 0x48c61718#32), by simpa [oneHotDifference] using cell_28_28⟩
  · exact ⟨0x00000000680000007fa37362144093f987d7f9a0f913705206ccb21340000001#256,
      (0xf5ae50ac#32, 0x5b65e495#32), by simpa [oneHotDifference] using cell_28_29⟩
  · exact ⟨0x0000000070000000f328c90c88f024cff96ab0474a8074da0e153f6170000040#256,
      (0xf5ab6b48#32, 0x84d970b8#32), by simpa [oneHotDifference] using cell_28_30⟩
  · exact ⟨0x000000005888200004ec637a598bfae3d8fddfd5021c858d114abcaca79e036c#256,
      (0xbc55d99e#32, 0x3f728922#32), by simpa [oneHotDifference] using cell_28_31⟩

end Magma.DiffanNineRoundPositiveRows
