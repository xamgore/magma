module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row04Group00
public import Magma.Differential.NinePlus.PositiveRows.Row04Group01
public import Magma.Differential.NinePlus.PositiveRows.Row04Group02
public import Magma.Differential.NinePlus.PositiveRows.Row04Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 4. -/
theorem row04 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (4 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000008648db05ed438dccaa18f202c2a1a5e42a723a2c53786bc75aeb26f#256,
      (0x13d74965#32, 0xb456101b#32), by simpa [oneHotDifference] using cell_04_00⟩
  · exact ⟨0x000000008fe1e0b700fc56ee8cdc2307608d89be021357cc7450196e4f722dae#256,
      (0x4bb7207e#32, 0x2389822b#32), by simpa [oneHotDifference] using cell_04_01⟩
  · exact ⟨0x00000000ecbba3378e74bb00dcf8e5842460e48aa2c7a49bcb29e87d32332623#256,
      (0x55923130#32, 0xe15e467a#32), by simpa [oneHotDifference] using cell_04_02⟩
  · exact ⟨0x0000000092fa650f947aa936a88a03ba4731a07088d6bb4faceadfad74b238cb#256,
      (0xf3dc194f#32, 0x197c303c#32), by simpa [oneHotDifference] using cell_04_03⟩
  · exact ⟨0x00000000d8e71ca5899a4dd8b8d32bfcecb8dcd3e868bab53848c6875e0d7470#256,
      (0x548f84fb#32, 0x998e8490#32), by simpa [oneHotDifference] using cell_04_04⟩
  · exact ⟨0x0000000061144cec0de19ccef6ee4fc0eea5171986afd1999597035d92e3857b#256,
      (0x226777b3#32, 0xc465c249#32), by simpa [oneHotDifference] using cell_04_05⟩
  · exact ⟨0x000000001a5b1f2c8ee5780987a06d08182bc9352e26923673746286f6fa2c66#256,
      (0x6829673b#32, 0x9c70fdcc#32), by simpa [oneHotDifference] using cell_04_06⟩
  · exact ⟨0x000000004d45e1af1f049f45b8942a48eb769460245404441baa0da8abc23db0#256,
      (0x3d12fd68#32, 0xb4f38280#32), by simpa [oneHotDifference] using cell_04_07⟩
  · exact ⟨0x00000000d8ff8030cb8cbd54cd3a348819414dbbf492e6e27105eb83a225d0ff#256,
      (0x5075cf0e#32, 0x0adad8c2#32), by simpa [oneHotDifference] using cell_04_08⟩
  · exact ⟨0x0000000077a53aed1668fa7d2535de1fa2643809e5d96f1fed8bb674c58797a0#256,
      (0x37355ece#32, 0x1a71d7fd#32), by simpa [oneHotDifference] using cell_04_09⟩
  · exact ⟨0x000000007eea47bf4457009f86c60e1ce5cdf9b414681844f50535fda857fd0f#256,
      (0xc74b1db2#32, 0xe1cb87d1#32), by simpa [oneHotDifference] using cell_04_10⟩
  · exact ⟨0x00000000b356466f9581889ca3ea99d41164766dcaaf3712b6a2f7e1c6b76ef8#256,
      (0xfbdc1d68#32, 0xc70128c1#32), by simpa [oneHotDifference] using cell_04_11⟩
  · exact ⟨0x00000000c36c70502c924d7eb598f2ab720ae1e726e4fa73d89308937a0287fe#256,
      (0x5970e214#32, 0xef94fc0a#32), by simpa [oneHotDifference] using cell_04_12⟩
  · exact ⟨0x000000008e40f5af0a81028d2760723febe86bafc27a47983f501e24ebabe00f#256,
      (0x1a5f4119#32, 0xb5b7bce7#32), by simpa [oneHotDifference] using cell_04_13⟩
  · exact ⟨0x00000000d8b5211771a61cadee4358ad902412757b1c479099169d8ca181b900#256,
      (0xf985b85a#32, 0x34074d90#32), by simpa [oneHotDifference] using cell_04_14⟩
  · exact ⟨0x0000000090ed0aee89691f236e78b48a3db9f9ed109c0a645216e4172d09b050#256,
      (0x21b8d339#32, 0xd38242a1#32), by simpa [oneHotDifference] using cell_04_15⟩
  · exact ⟨0x00000000baa5d9162016d2f8302d360d5e23128a2984a9cceaabf4cd89c94bf2#256,
      (0x155057d6#32, 0xf4461aa8#32), by simpa [oneHotDifference] using cell_04_16⟩
  · exact ⟨0x000000009c23598f84dc12eeb86df9f6edf8e8292001a1729e72eef5b2cd9f80#256,
      (0x86eafc9c#32, 0x517fae76#32), by simpa [oneHotDifference] using cell_04_17⟩
  · exact ⟨0x0000000018344c3782105833b23fa5d2d5f7331da434196a49bc7ce34523ffc0#256,
      (0x8008b0ec#32, 0xbfed630c#32), by simpa [oneHotDifference] using cell_04_18⟩
  · exact ⟨0x00000000d3d093c2236650d315533e68bb5c3d6a62dc6564d5ec82a858a8c3f0#256,
      (0xb3dfb502#32, 0xb8203cd4#32), by simpa [oneHotDifference] using cell_04_19⟩
  · exact ⟨0x000000001ba84cf3ca656e3160b3fe12408b9e82128e7bc3ecb2c4efc4cef8c0#256,
      (0x05b55fff#32, 0xccc18c6a#32), by simpa [oneHotDifference] using cell_04_20⟩
  · exact ⟨0x0000000015deba97a714e9fd12a9a38e0a5177e0b502ec978006a4bd53586f50#256,
      (0x41578e6b#32, 0xbead0fd7#32), by simpa [oneHotDifference] using cell_04_21⟩
  · exact ⟨0x0000000037c17f88d2cb7c1f84eeb7df5317ae7537e1c18a8475eb7e1e2bd100#256,
      (0x9596000d#32, 0x41ceb28c#32), by simpa [oneHotDifference] using cell_04_22⟩
  · exact ⟨0x0000000090c7979fee0bfa051a1f049b67e6918dc3cb3d3f0f4b86091780fc0d#256,
      (0x5297f3f9#32, 0x1659f5fd#32), by simpa [oneHotDifference] using cell_04_23⟩
  · exact ⟨0x00000000153576d158f12b2cb789f129b33b23a1c7bf74019ef0a272ae0f7f00#256,
      (0xd908c439#32, 0xa22ea8a7#32), by simpa [oneHotDifference] using cell_04_24⟩
  · exact ⟨0x000000006d18464f2dd5c23de295d6934ae3f179c6f187ba47c8e7b9efffff80#256,
      (0xf6aa6bd9#32, 0x87cf95c4#32), by simpa [oneHotDifference] using cell_04_25⟩
  · exact ⟨0x000000006d7be9d0e7c9d99d5f3d24bb4d7bf70531f6d9f69627dbfafb013040#256,
      (0x6490ceb1#32, 0x0e472346#32), by simpa [oneHotDifference] using cell_04_26⟩
  · exact ⟨0x0000000043561e77bb20bfb69b410682804ea9e38775dcdc87efaa8f18341f0d#256,
      (0x6892248e#32, 0xa6781ab9#32), by simpa [oneHotDifference] using cell_04_27⟩
  · exact ⟨0x000000004c27d9b482598c8fd11a984e3dcedf36e4fafa13a084229bf0e77560#256,
      (0x86fbcfdc#32, 0x7e18abba#32), by simpa [oneHotDifference] using cell_04_28⟩
  · exact ⟨0x00000000907be40f6320d7e227a1f2b092f80bea33bf3cb2a4e2d4f1ff878fff#256,
      (0xf044caa9#32, 0xf0b54384#32), by simpa [oneHotDifference] using cell_04_29⟩
  · exact ⟨0x000000001fedd39779ac4513b08c61f2497f17a638829b95bf32d47dcff8fdcf#256,
      (0xfa448266#32, 0xd2cdf8d5#32), by simpa [oneHotDifference] using cell_04_30⟩
  · exact ⟨0x00000000ffb2c7c5aaa6885729e7defec1571aa4145517902252132acfd815b5#256,
      (0x1c9ba3e8#32, 0x1d9dc6dd#32), by simpa [oneHotDifference] using cell_04_31⟩

end Magma.DiffanNineRoundPositiveRows
