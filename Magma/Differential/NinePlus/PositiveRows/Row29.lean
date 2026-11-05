module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row29Group00
public import Magma.Differential.NinePlus.PositiveRows.Row29Group01
public import Magma.Differential.NinePlus.PositiveRows.Row29Group02
public import Magma.Differential.NinePlus.PositiveRows.Row29Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 29. -/
theorem row29 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (29 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000010010000afb662895493fb2e41d7dac4c9f49c9edf4189c2d1427c27#256,
      (0x67d8f08e#32, 0x40146a00#32), by simpa [oneHotDifference] using cell_29_00⟩
  · exact ⟨0x0000000060ffffff5331b48b510471cfbbf93f978c1744fa64cf534e008acd3a#256,
      (0xdb1eac04#32, 0xfb056569#32), by simpa [oneHotDifference] using cell_29_01⟩
  · exact ⟨0x0000000078038000925c369f0926cc9bd54842c0f69396b6761a618aeb9e7f5e#256,
      (0x08ca2583#32, 0x3d66e7d3#32), by simpa [oneHotDifference] using cell_29_02⟩
  · exact ⟨0x0000000040002000470fe51e334b928727ff9788074079753d36e5caa19c41aa#256,
      (0xf25c48be#32, 0x41059f80#32), by simpa [oneHotDifference] using cell_29_03⟩
  · exact ⟨0x00000000600020008cee351862381df13e3123008fb5e47d3a775fe17304bf30#256,
      (0x5d145971#32, 0xe706dfd5#32), by simpa [oneHotDifference] using cell_29_04⟩
  · exact ⟨0x00000000765897ffc5010506e32ffce83103604baa96ea2767cdc4efbde27413#256,
      (0x479554f8#32, 0xf4b3325b#32), by simpa [oneHotDifference] using cell_29_05⟩
  · exact ⟨0x00000000000e6179cb857f5c84d13ca9d6fbbecac36f908ecfd867752e60b232#256,
      (0x698b997a#32, 0xe9cfa0ec#32), by simpa [oneHotDifference] using cell_29_06⟩
  · exact ⟨0x00000000f800f00052e0b4ffc79a7ecea693d4e5a7fa51b94e567b8b1f50a990#256,
      (0x5af8a038#32, 0xa853e8db#32), by simpa [oneHotDifference] using cell_29_07⟩
  · exact ⟨0x0000000080d000001fe8bd7bf3e68ac8c16f0bc658b84b9f14f971b3c9aa8900#256,
      (0x875ab24d#32, 0x976d7820#32), by simpa [oneHotDifference] using cell_29_08⟩
  · exact ⟨0x000000005af7f8bf212a2907aaa42be67291e6e156e0a5b917893b0ad4919af6#256,
      (0xd804fc23#32, 0x33911d54#32), by simpa [oneHotDifference] using cell_29_09⟩
  · exact ⟨0x0000000000000000b8ed8cf7fe8d953b57663532157fdd336bad78352a307a00#256,
      (0x99d08035#32, 0x812ec62d#32), by simpa [oneHotDifference] using cell_29_10⟩
  · exact ⟨0x00000000c0000000a42194e8f6f7efcb5c12dfa601783170cdafbcc01993cd00#256,
      (0x8f0e8290#32, 0x9347eed5#32), by simpa [oneHotDifference] using cell_29_11⟩
  · exact ⟨0x00000000de03000099266518d8473429a80ce3e2db2c2a4a038844e4e4818800#256,
      (0x1ebb08d8#32, 0x7ac2a8ad#32), by simpa [oneHotDifference] using cell_29_12⟩
  · exact ⟨0x00000000d0000000085ed3e5767e66251901ad8963b6a7a52c782d5b80caa000#256,
      (0xc164c200#32, 0x226d7277#32), by simpa [oneHotDifference] using cell_29_13⟩
  · exact ⟨0x000000009c38243660f3346fdaf2496257c33ca5b45c078728b03616e820c200#256,
      (0xe785f0e6#32, 0xb27d8f61#32), by simpa [oneHotDifference] using cell_29_14⟩
  · exact ⟨0x000000001c000000414c7c26bf0e005752848d61fac52fd077e403c3e2409800#256,
      (0xc24e0d27#32, 0x2c0f1922#32), by simpa [oneHotDifference] using cell_29_15⟩
  · exact ⟨0x0000000000000000d2ba3dad179f6765b271cbaf2cd0eeab59cec3bc75c68000#256,
      (0x35430a84#32, 0xaffe4095#32), by simpa [oneHotDifference] using cell_29_16⟩
  · exact ⟨0x000000001017b0005f1161fc054f64ab46fcb968e8108c8bc2cebbbcbecd66d0#256,
      (0xc252fffa#32, 0x4ca9c132#32), by simpa [oneHotDifference] using cell_29_17⟩
  · exact ⟨0x000000005c000800e338fa7c2701e09086be9470968cf83b3f548048b67c8500#256,
      (0xf150b9de#32, 0xed540dd9#32), by simpa [oneHotDifference] using cell_29_18⟩
  · exact ⟨0x00000000dcff800070eed63d4b9f25ff7b923d1ad5f6b8a1efac8e1b5218fef8#256,
      (0x53120e84#32, 0x950dd6c6#32), by simpa [oneHotDifference] using cell_29_19⟩
  · exact ⟨0x00000000200000005c1c323fba5ef282bddb26faa4eb45256c5dc00ce54e0004#256,
      (0x1577c738#32, 0x73b4af24#32), by simpa [oneHotDifference] using cell_29_20⟩
  · exact ⟨0x00000000700e00009d2e0c2b01bbf7652444f38d558e75db07db119091b00000#256,
      (0x94ed08ef#32, 0x1cf2b99c#32), by simpa [oneHotDifference] using cell_29_21⟩
  · exact ⟨0x0000000030877e00f7fbf48386021b7cfd7a09ec160cff137a41acce683f7005#256,
      (0x7d39885e#32, 0xb79d962b#32), by simpa [oneHotDifference] using cell_29_22⟩
  · exact ⟨0x00000000c7ffc000728acc6ee7bc35614907b6cdc023babe7fab0252c470cc00#256,
      (0x5161aaa7#32, 0xaa1af4ce#32), by simpa [oneHotDifference] using cell_29_23⟩
  · exact ⟨0x00000000200f8000b3543e3ab73f0e70c11f5649cb6bfe9c03ec90ea1234ef08#256,
      (0xda01acfa#32, 0xcb5df9e9#32), by simpa [oneHotDifference] using cell_29_24⟩
  · exact ⟨0x0000000000fff0002b826486145150b689940710be09ec569e8501cba1f30fff#256,
      (0x9d16a389#32, 0x2f6e5662#32), by simpa [oneHotDifference] using cell_29_25⟩
  · exact ⟨0x0000000050d0000079836b70bac6fc6fea6ec5284227044616708d9bbdff0060#256,
      (0xdd018cc0#32, 0x542adb00#32), by simpa [oneHotDifference] using cell_29_26⟩
  · exact ⟨0x00000000b00000008f6ed19275615d19aa8e124f7fbba00d7771e1df26000008#256,
      (0xa0a85d39#32, 0xc20b10ba#32), by simpa [oneHotDifference] using cell_29_27⟩
  · exact ⟨0x000000007c0300009493cc6da1e8c5d19c25267ad24b236aacc04d786e000800#256,
      (0x6a463e95#32, 0x95610a02#32), by simpa [oneHotDifference] using cell_29_28⟩
  · exact ⟨0x00000000b800000051177652023bbd48cdfc18bbc0165fc2d2292ab41800a000#256,
      (0x905713f2#32, 0xe55932dd#32), by simpa [oneHotDifference] using cell_29_29⟩
  · exact ⟨0x0000000017e00000c9059a35d9382e23ce9d0be6d144f2eba68efc92502c0000#256,
      (0x99bbe904#32, 0xb7e0f151#32), by simpa [oneHotDifference] using cell_29_30⟩
  · exact ⟨0x000000003000a04027f7ebe46c93ff5c65922e92890a8b1fee6495904bbd18d6#256,
      (0x4202225e#32, 0x6fba4819#32), by simpa [oneHotDifference] using cell_29_31⟩

end Magma.DiffanNineRoundPositiveRows
