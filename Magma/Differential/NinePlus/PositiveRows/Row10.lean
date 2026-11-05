module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row10Group00
public import Magma.Differential.NinePlus.PositiveRows.Row10Group01
public import Magma.Differential.NinePlus.PositiveRows.Row10Group02
public import Magma.Differential.NinePlus.PositiveRows.Row10Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 10. -/
theorem row10 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (10 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000005ae645825102026d4f51e75d5151526d01675741c4c3877c4565b6ed#256,
      (0xce0227d8#32, 0x997271bd#32), by simpa [oneHotDifference] using cell_10_00⟩
  · exact ⟨0x00000000855a4bffb8ee56863830ec732118ff53b04e414ad8adaacdc809b8c1#256,
      (0xa0c7196d#32, 0xbab52c65#32), by simpa [oneHotDifference] using cell_10_01⟩
  · exact ⟨0x00000000946a9dcfa21da08dd44fc93d88a445535804a0bcd6b9cccddc7d3632#256,
      (0x9bc18001#32, 0xe8bb2c40#32), by simpa [oneHotDifference] using cell_10_02⟩
  · exact ⟨0x00000000868ef72c5f289d0c1923433633d71eba72863ebb169b358c5dc8a9f5#256,
      (0xe5c9df32#32, 0x17d7ea84#32), by simpa [oneHotDifference] using cell_10_03⟩
  · exact ⟨0x00000000a943feb0c97ba2cd4354d2b108bc1b726f6bcb3fe9c8aeef9c61d788#256,
      (0xae885bdf#32, 0x92f7de16#32), by simpa [oneHotDifference] using cell_10_04⟩
  · exact ⟨0x000000008fa03500049eedfb3678b38a45458945136c58defe14636a736fdea0#256,
      (0x647a6b1f#32, 0x8918e3c1#32), by simpa [oneHotDifference] using cell_10_05⟩
  · exact ⟨0x000000006bc3be50b67851bd8d0610737807a21e37b83c9d2ba0a3de31617756#256,
      (0xe9dab0db#32, 0x4f7976d8#32), by simpa [oneHotDifference] using cell_10_06⟩
  · exact ⟨0x00000000fc9ac2ff3929d01683837317aae89a39416a07a05cf0077a25a775b0#256,
      (0x75a251f9#32, 0x047a439a#32), by simpa [oneHotDifference] using cell_10_07⟩
  · exact ⟨0x00000000a9308b00cceee5ba82b4d435df6028030fb92ceb2150015fb70b2b00#256,
      (0x8c6b188d#32, 0x9f45bb1a#32), by simpa [oneHotDifference] using cell_10_08⟩
  · exact ⟨0x00000000d6c5a40fdac5bff32974e991c40754e56deade7fd0f6dbdd6c4eb1f8#256,
      (0xd05975a3#32, 0xa062de05#32), by simpa [oneHotDifference] using cell_10_09⟩
  · exact ⟨0x000000009299baff8c1e035fc35591ad8a19df37090fb9e3463aa67a45192d00#256,
      (0xee634503#32, 0xd079c35c#32), by simpa [oneHotDifference] using cell_10_10⟩
  · exact ⟨0x00000000211037729093bacbf35965deab35b654908d5e32f12c42526a3fb434#256,
      (0x09a80d72#32, 0xe86c53f9#32), by simpa [oneHotDifference] using cell_10_11⟩
  · exact ⟨0x000000003e7544ffbdc8105edd63610979ccb87e1f4b5983fbd9d868612c898f#256,
      (0x291d1a40#32, 0x942e06f1#32), by simpa [oneHotDifference] using cell_10_12⟩
  · exact ⟨0x000000001c2ae2ff4d32bba06730ed00c76b8f1fc17b57ca1fe6db340fa06fc7#256,
      (0x0f83028c#32, 0x7f82167d#32), by simpa [oneHotDifference] using cell_10_13⟩
  · exact ⟨0x00000000a1e6a1007bd52a8efc821a25de6d76d791bcffabab4b012ad96cb000#256,
      (0x1bd6932a#32, 0xc4a4edf7#32), by simpa [oneHotDifference] using cell_10_14⟩
  · exact ⟨0x00000000f51d93ff1728c14db49033f91745f5fadfac591971c1b59528538ff8#256,
      (0x74302e4b#32, 0x8bfde6a9#32), by simpa [oneHotDifference] using cell_10_15⟩
  · exact ⟨0x000000005a6cac00e52c146ff30699037d7d46a8108084faa00116033fd2b400#256,
      (0xbb5a19f0#32, 0x7d9c4d27#32), by simpa [oneHotDifference] using cell_10_16⟩
  · exact ⟨0x00000000519773f08cbffb3ea5c6c2d6921036d216db05203a5c181e7dc0ffdf#256,
      (0x75a9e459#32, 0x55d7832a#32), by simpa [oneHotDifference] using cell_10_17⟩
  · exact ⟨0x00000000855c8a513ebd730187328f71de373fbdf2a9dc633c897650c0d40187#256,
      (0x2f8e3434#32, 0x15bba259#32), by simpa [oneHotDifference] using cell_10_18⟩
  · exact ⟨0x00000000c40932ffae9e348404694f1f7093346feb50d62c04bf1ee02c7bffff#256,
      (0xa2350ba7#32, 0x69ecc3b9#32), by simpa [oneHotDifference] using cell_10_19⟩
  · exact ⟨0x000000004a445cffdfb390c009945b5c608ebdd066990ad00d1a76cd27777fff#256,
      (0xfbbac2d5#32, 0x30a50f20#32), by simpa [oneHotDifference] using cell_10_20⟩
  · exact ⟨0x00000000830dc43e112ba83095103878bb72fcb380daa32ed3690a56f4961080#256,
      (0x540a9efa#32, 0xcff24581#32), by simpa [oneHotDifference] using cell_10_21⟩
  · exact ⟨0x00000000f1ef90ff17bbf76e56c7acaa9479e75eb6d0dcffb801146b002fffff#256,
      (0x9c929ff5#32, 0x08f93f68#32), by simpa [oneHotDifference] using cell_10_22⟩
  · exact ⟨0x0000000080653f0073cb5cfd480411952fb9ed79baaa24b4c116b974b6a40000#256,
      (0x71e7c18f#32, 0xff17055c#32), by simpa [oneHotDifference] using cell_10_23⟩
  · exact ⟨0x00000000bbb69a7f12e0f693d47cbd4aa5cbe78f64d5126e9cd10c4d310270c4#256,
      (0x8d1fe337#32, 0xfa2126dc#32), by simpa [oneHotDifference] using cell_10_24⟩
  · exact ⟨0x00000000da2c347f597ccbf27934a8d946abd90e43b719d713efa46326efff80#256,
      (0x5f72f92b#32, 0xa532bb22#32), by simpa [oneHotDifference] using cell_10_25⟩
  · exact ⟨0x00000000ebf93b00cc09b95c6a04f5167a35112491fc9fa280e5c9a4abf00000#256,
      (0x1f0eb9ff#32, 0x42ec79ee#32), by simpa [oneHotDifference] using cell_10_26⟩
  · exact ⟨0x000000008a625aff15c65e6b83e29b16ef0712fe82068379f85b6431fbbae9c0#256,
      (0x1a38fbe8#32, 0xd6da2856#32), by simpa [oneHotDifference] using cell_10_27⟩
  · exact ⟨0x00000000879bcbff827d51b1258dd710124bde8659651350944bcd75a1888707#256,
      (0x67afb50e#32, 0x528900bc#32), by simpa [oneHotDifference] using cell_10_28⟩
  · exact ⟨0x00000000ed4698ff93dfb31034c9ca3ff35dc7fd85d7b6b80cf9f3be300c9833#256,
      (0x7d485c03#32, 0xb762682b#32), by simpa [oneHotDifference] using cell_10_29⟩
  · exact ⟨0x00000000e8b9d300116570044cd1b641950ab697210815aa0e1433e038000000#256,
      (0xb20b85e2#32, 0x07c4f1c5#32), by simpa [oneHotDifference] using cell_10_30⟩
  · exact ⟨0x000000001b9dafffa41285884a8ba4b8fa39167ee8661b7fe3278989ca14662c#256,
      (0xf7fae3a7#32, 0x2165ff60#32), by simpa [oneHotDifference] using cell_10_31⟩

end Magma.DiffanNineRoundPositiveRows
