module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row17Group00
public import Magma.Differential.NinePlus.PositiveRows.Row17Group01
public import Magma.Differential.NinePlus.PositiveRows.Row17Group02
public import Magma.Differential.NinePlus.PositiveRows.Row17Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 17. -/
theorem row17 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (17 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000051db7dfaed7df51e323132d78def1d798ae7ab4864c9a1abe240a963#256,
      (0xa9bf0ca6#32, 0x9e336125#32), by simpa [oneHotDifference] using cell_17_00⟩
  · exact ⟨0x00000000f954fffebdac30be6814ede8bdfa6e68a84b332ee0e03c9df161175e#256,
      (0x548902fd#32, 0x5abadba4#32), by simpa [oneHotDifference] using cell_17_01⟩
  · exact ⟨0x0000000032f9f3c15db30d9b42c98fd371a2be8be4c3635d1aaeadca7c762719#256,
      (0x79ab1688#32, 0xc71dfadd#32), by simpa [oneHotDifference] using cell_17_02⟩
  · exact ⟨0x000000006ff685ffefab4b0042b45719667194f13f632bb83c252685f488dada#256,
      (0xebc9366e#32, 0x768c8306#32), by simpa [oneHotDifference] using cell_17_03⟩
  · exact ⟨0x0000000081eae3ff865f7c1c887e5bb6fb04e445d94ff0ec9f8a83f3a9fb11f0#256,
      (0x58a0abd2#32, 0x977b6c42#32), by simpa [oneHotDifference] using cell_17_04⟩
  · exact ⟨0x0000000029ed3fffc2aeaf075459402055b60da87dbb7eb97fa7423c261cfeaf#256,
      (0x6d623fc7#32, 0x1825783d#32), by simpa [oneHotDifference] using cell_17_05⟩
  · exact ⟨0x00000000abe25e218081382feb3c81562dc5d5a560a2f545b73971c0461fb040#256,
      (0x6d477bdc#32, 0xf0982036#32), by simpa [oneHotDifference] using cell_17_06⟩
  · exact ⟨0x00000000e79cffffa7122aa46538389d8411d14f8fe7a060804adefd9c3ef94f#256,
      (0x8b5cfcd8#32, 0x29f7da98#32), by simpa [oneHotDifference] using cell_17_07⟩
  · exact ⟨0x00000000d8f53fff5ec91da422eeeddee1031e4d88dc425a7347c3da95011efe#256,
      (0x4ad93b4e#32, 0xcc01f6b0#32), by simpa [oneHotDifference] using cell_17_08⟩
  · exact ⟨0x000000003e607ffec879e63d235dda70a0e9e2692db5601fa4923f970aa63e0b#256,
      (0x2ef2efb4#32, 0x3388a758#32), by simpa [oneHotDifference] using cell_17_09⟩
  · exact ⟨0x00000000ae223f52b52ecae06f3bb5e1a33067de5a1617dbc4405c5eee0c319c#256,
      (0x061bd6b1#32, 0x919e634c#32), by simpa [oneHotDifference] using cell_17_10⟩
  · exact ⟨0x000000006becfffff8520fedc0dcd46c744208b9b7daaba5115678638b477382#256,
      (0x234b3d05#32, 0xc222d169#32), by simpa [oneHotDifference] using cell_17_11⟩
  · exact ⟨0x000000002c55ffffd8487360ea905646ab10499dbcc3cdf197865b5d2aacef78#256,
      (0xdb1ef717#32, 0xfb7c3ecd#32), by simpa [oneHotDifference] using cell_17_12⟩
  · exact ⟨0x00000000bc2cffffee2e5b079af7680612fe7336b2c37ab24b206d40347fb002#256,
      (0x50b6fbfa#32, 0x1f8d7c56#32), by simpa [oneHotDifference] using cell_17_13⟩
  · exact ⟨0x000000002215fffff29aad3cfc2e01f3fc6d78c19de7943bc4943ecc1f37d704#256,
      (0xa5a7385a#32, 0xe9ca9d47#32), by simpa [oneHotDifference] using cell_17_14⟩
  · exact ⟨0x00000000716a01ff6e4ae1ab51aa39b3c4933e3c3d680948e4c0c3ee190d7d85#256,
      (0x2558f317#32, 0x2d918d7f#32), by simpa [oneHotDifference] using cell_17_15⟩
  · exact ⟨0x000000000edaffff5ab7004918c4053be36abc7314e1f458797e6139c90f007c#256,
      (0xfff72854#32, 0xaf2ae607#32), by simpa [oneHotDifference] using cell_17_16⟩
  · exact ⟨0x0000000059923fff7b720a04ee5f4364962b850c220b61405eba7df8b2de2fe0#256,
      (0x38e889ff#32, 0x422c4f7c#32), by simpa [oneHotDifference] using cell_17_17⟩
  · exact ⟨0x000000001441b42f1acf1e7f633658d0594cdcd78037d448a4973eadb8eda0e0#256,
      (0x9132d46b#32, 0xe920b94b#32), by simpa [oneHotDifference] using cell_17_18⟩
  · exact ⟨0x000000002f3f0000b0331415ceafa1744625c8340f882b51f0b65e013ad30000#256,
      (0x7cae7d1d#32, 0x66cb7741#32), by simpa [oneHotDifference] using cell_17_19⟩
  · exact ⟨0x000000004cfb0000f5e6257d89df65ff5f03aeeae57e863ee755de78ce8f8000#256,
      (0xf2c13c62#32, 0x70c383fa#32), by simpa [oneHotDifference] using cell_17_20⟩
  · exact ⟨0x000000004bcb0000d418f8222af1607a07a94acd6d1b9ca0c0487f4431d00000#256,
      (0x039fa668#32, 0xbdef7ab0#32), by simpa [oneHotDifference] using cell_17_21⟩
  · exact ⟨0x00000000e29a4d0991b7166d36b707ea9ce92a573e8ba1a62d15b631f6309000#256,
      (0xf1216b88#32, 0x3773d3fb#32), by simpa [oneHotDifference] using cell_17_22⟩
  · exact ⟨0x0000000026ed00007c8404769c08755b8c57f67fbab0829d93df77aa93900000#256,
      (0xdc341e85#32, 0x6254ab5f#32), by simpa [oneHotDifference] using cell_17_23⟩
  · exact ⟨0x00000000f6ed800011cea94b8c7ba5fc842c6b9207bdb6005a41636b9d080000#256,
      (0xc175a68d#32, 0xa3e2637a#32), by simpa [oneHotDifference] using cell_17_24⟩
  · exact ⟨0x00000000fa29fffce2a183cc64ff113f93933ba0f9dea144e770349ba095c000#256,
      (0x7539edb5#32, 0xec6837f2#32), by simpa [oneHotDifference] using cell_17_25⟩
  · exact ⟨0x000000006d220500cc9672f27ffc952bbf15a0d1a425b2db74ac44d0a1412010#256,
      (0xde34d057#32, 0xa671e70f#32), by simpa [oneHotDifference] using cell_17_26⟩
  · exact ⟨0x00000000426cffff7025734b264bb0003a01acd4ace622eae6352aa019c06000#256,
      (0x1e68cace#32, 0x4d6f8533#32), by simpa [oneHotDifference] using cell_17_27⟩
  · exact ⟨0x000000008bd67dd8ce378e6f55d87612aa2786d540c762ba488fe154260d70c0#256,
      (0x6245ccfd#32, 0x5a9f4a51#32), by simpa [oneHotDifference] using cell_17_28⟩
  · exact ⟨0x000000008c15000007f2cccf65dead8e2ae6553844753f6d6aa2a66400000800#256,
      (0x6bd660d2#32, 0xce2a5afa#32), by simpa [oneHotDifference] using cell_17_29⟩
  · exact ⟨0x00000000047e38007b37754a2c231299601815ee5afe8cb4a26394a4f82ba000#256,
      (0xf55a87e0#32, 0x3891402d#32), by simpa [oneHotDifference] using cell_17_30⟩
  · exact ⟨0x000000000fab00004f74b3376b5ffd107c451bfeedb02b24ac340c802d465fc8#256,
      (0xba36a234#32, 0xd1755ce6#32), by simpa [oneHotDifference] using cell_17_31⟩

end Magma.DiffanNineRoundPositiveRows
