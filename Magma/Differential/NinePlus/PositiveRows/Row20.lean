module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row20Group00
public import Magma.Differential.NinePlus.PositiveRows.Row20Group01
public import Magma.Differential.NinePlus.PositiveRows.Row20Group02
public import Magma.Differential.NinePlus.PositiveRows.Row20Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 20. -/
theorem row20 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (20 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000dff00000bb47ed7245a6a7ebd71d81b0388624e54489298d617c4ba9#256,
      (0x4d31482b#32, 0xca345e15#32), by simpa [oneHotDifference] using cell_20_00⟩
  · exact ⟨0x0000000007f37ff9ed361ef9cd703b85cc87dfd33172816749b754f272f7845b#256,
      (0x9d1524f6#32, 0x6fffa92b#32), by simpa [oneHotDifference] using cell_20_01⟩
  · exact ⟨0x000000004f0fffff45f68b0ee3f68b15737b02d1708d4790fe9eea690feca7f3#256,
      (0x3059ae09#32, 0x17143bd8#32), by simpa [oneHotDifference] using cell_20_02⟩
  · exact ⟨0x00000000abd7ffff415c4fc1f09cc35a8649a8e170f9440475da4a3ee3d89396#256,
      (0xbe0349cd#32, 0xd34bd10f#32), by simpa [oneHotDifference] using cell_20_03⟩
  · exact ⟨0x00000000e1370796a531440665e330a345ad15bddf38b4bc4fafb21b1815b1d0#256,
      (0x55923460#32, 0xf6dc7369#32), by simpa [oneHotDifference] using cell_20_04⟩
  · exact ⟨0x000000008e6c3ffe4a3bb5cb6d5e77a008609d9f9bd69a44ebf53ef59c0d8bb0#256,
      (0xb76767f2#32, 0x384f4c66#32), by simpa [oneHotDifference] using cell_20_05⟩
  · exact ⟨0x0000000039b44efb43fa5abcadbcf3b091cadb534d5c05d2344ee4276b47ed50#256,
      (0x90f006f1#32, 0x98734b22#32), by simpa [oneHotDifference] using cell_20_06⟩
  · exact ⟨0x00000000a6dc0000769f7981cd89bcc8e1f44fcba3a8557d5d918e8065486040#256,
      (0x89ed9410#32, 0x55363a3c#32), by simpa [oneHotDifference] using cell_20_07⟩
  · exact ⟨0x00000000b3f08000a2c2f64ddd10c06270da68ccbe1fb11546ed5800f9d387c0#256,
      (0x1e8fc134#32, 0x96eeb45c#32), by simpa [oneHotDifference] using cell_20_08⟩
  · exact ⟨0x000000008eccaf0280f97beef3efdac4712811fa880e1ec8427899e8c7dae5d0#256,
      (0x99d2e4ee#32, 0xf2e13c45#32), by simpa [oneHotDifference] using cell_20_09⟩
  · exact ⟨0x00000000cc4fffff7d43b361cc1d294207a12cb13de6f41c95feb547cbf16bf8#256,
      (0x8d773135#32, 0xca1c43b2#32), by simpa [oneHotDifference] using cell_20_10⟩
  · exact ⟨0x0000000090c7305ec4a340c2ac8e1821ea3b50be05ff633b1c1264f1f721f880#256,
      (0x11ba47be#32, 0x8e67448c#32), by simpa [oneHotDifference] using cell_20_11⟩
  · exact ⟨0x000000004848000048d792383a44cc6e8b749f39bb91074710641f76414aab00#256,
      (0xac07b5ae#32, 0x0e118adf#32), by simpa [oneHotDifference] using cell_20_12⟩
  · exact ⟨0x00000000b98cffff52064ec154a208ecce8ffa329b2711c121fe69924056dc40#256,
      (0x99fe3773#32, 0xfcb03f4e#32), by simpa [oneHotDifference] using cell_20_13⟩
  · exact ⟨0x000000008ecfff7f9fe4b10a6dd0c0003de9078d493775634d3aebd6a519cfff#256,
      (0xa4213ce1#32, 0x7fcda4be#32), by simpa [oneHotDifference] using cell_20_14⟩
  · exact ⟨0x000000008d7ed9faa19005c9d051146c535281c05c070f980b0113fd3be57402#256,
      (0xd7c0af4a#32, 0x191fa33f#32), by simpa [oneHotDifference] using cell_20_15⟩
  · exact ⟨0x00000000836e0000bf9b3aa96f9e70ade6be0bb431f892da06b5f5d888935f00#256,
      (0x74b05c1a#32, 0x2c429b0c#32), by simpa [oneHotDifference] using cell_20_16⟩
  · exact ⟨0x0000000061d000003d327caea7e74d266bb5f0808107e9f4524775be64890000#256,
      (0xfa30e540#32, 0x08861f6a#32), by simpa [oneHotDifference] using cell_20_17⟩
  · exact ⟨0x00000000e86fffff920f43e2182c9548ac7e06e565317a23a7c9e8f5ddcafcff#256,
      (0x61cdcc58#32, 0x24c303dc#32), by simpa [oneHotDifference] using cell_20_18⟩
  · exact ⟨0x000000004b89fff27870b3b68ef2fbdf9e61f284eaa5b5e0aced99ef7e09c64f#256,
      (0x79aba8bc#32, 0x0f508670#32), by simpa [oneHotDifference] using cell_20_19⟩
  · exact ⟨0x0000000020ac000044082b1147273925c8350c56b20622abac8336d059b00000#256,
      (0x14518e53#32, 0xd20a7442#32), by simpa [oneHotDifference] using cell_20_20⟩
  · exact ⟨0x00000000efc80000c907fd8d21d0eb2085592971642286c241b1f08b8ef00000#256,
      (0xfead8154#32, 0x80354f5d#32), by simpa [oneHotDifference] using cell_20_21⟩
  · exact ⟨0x00000000a58c0000ef15c2addfb6d5fd67b0867a0a17225afcec1d790eb00000#256,
      (0x6da1ff94#32, 0x190be3f3#32), by simpa [oneHotDifference] using cell_20_22⟩
  · exact ⟨0x000000001c6fffffccf44cb09fc5a5dbb1c541958e3e1ab01e7b54e7307147ef#256,
      (0xfdbbe478#32, 0x2d9adafa#32), by simpa [oneHotDifference] using cell_20_23⟩
  · exact ⟨0x000000002aec00000f2217109af78c1e93e7d3fcfc335747e95e11df48c60000#256,
      (0x3120854f#32, 0xc1261bfd#32), by simpa [oneHotDifference] using cell_20_24⟩
  · exact ⟨0x00000000da6f0000827f8ec72e76bc3a13c3341ceb957d8288513cb029800000#256,
      (0x4c446121#32, 0x9735c355#32), by simpa [oneHotDifference] using cell_20_25⟩
  · exact ⟨0x00000000db2be0006f4858519aea665ff4c1925157ebd8848d5e7b882b000000#256,
      (0x9799d39d#32, 0x23d470da#32), by simpa [oneHotDifference] using cell_20_26⟩
  · exact ⟨0x000000009f500000f4694f885e3a0f1428d64290cca3ed478e08c4c25d000000#256,
      (0xfc1547c0#32, 0x0015ebcf#32), by simpa [oneHotDifference] using cell_20_27⟩
  · exact ⟨0x00000000922e0080420669dd06b8758af3c158878d18a26999f11b4ede008000#256,
      (0x9fc9320c#32, 0xc275d109#32), by simpa [oneHotDifference] using cell_20_28⟩
  · exact ⟨0x0000000072b000005dd3b5a900602f67886655b213249a92016c0da6fc000000#256,
      (0xa369e6d1#32, 0x447c1b88#32), by simpa [oneHotDifference] using cell_20_29⟩
  · exact ⟨0x000000006e977800df71f67a3a1f9c6c955e155534e633ea757c5b0df80d0000#256,
      (0x5a6085c4#32, 0xc0b55f3e#32), by simpa [oneHotDifference] using cell_20_30⟩
  · exact ⟨0x00000000e9d7f00043769dbe65c2895a43bb0e35fdf50ddbad5b9c00e0195c9e#256,
      (0xf50a1de3#32, 0x20b3721c#32), by simpa [oneHotDifference] using cell_20_31⟩

end Magma.DiffanNineRoundPositiveRows
