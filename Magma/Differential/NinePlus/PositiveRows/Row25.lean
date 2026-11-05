module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row25Group00
public import Magma.Differential.NinePlus.PositiveRows.Row25Group01
public import Magma.Differential.NinePlus.PositiveRows.Row25Group02
public import Magma.Differential.NinePlus.PositiveRows.Row25Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 25. -/
theorem row25 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (25 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000107fffffb75715da20c57006e17ad881c1e6a0767e72d4a69bcac25f#256,
      (0xec95a62d#32, 0x95a08fd6#32), by simpa [oneHotDifference] using cell_25_00⟩
  · exact ⟨0x0000000032e0ffff780253bce77fba9c40a9b86bd209ff1e673895609bc41e96#256,
      (0x27d731e9#32, 0x553c8d6c#32), by simpa [oneHotDifference] using cell_25_01⟩
  · exact ⟨0x00000000d1f3b50c04853d6993e40664b11382890e7be4eb16bb1030320fef1e#256,
      (0x37ed1a86#32, 0x81a53836#32), by simpa [oneHotDifference] using cell_25_02⟩
  · exact ⟨0x00000000e24c4fff6085f4863a6f011ce420651993a30c8d949c89ea30b0e063#256,
      (0x1371129c#32, 0x8edadc6b#32), by simpa [oneHotDifference] using cell_25_03⟩
  · exact ⟨0x000000007777c597d9577f83875be6f2244caf8436a82d06e34d4e038483f088#256,
      (0x23686149#32, 0xf3f77480#32), by simpa [oneHotDifference] using cell_25_04⟩
  · exact ⟨0x000000009510f39c0a99e29563c107a82350827b4f6dfdb15e9944d6e204c952#256,
      (0x13c1b983#32, 0xc7b9919c#32), by simpa [oneHotDifference] using cell_25_05⟩
  · exact ⟨0x000000009e5881e2060e1747a3c398f32c1a336b96529c7f2df5d7c33e041c90#256,
      (0xa81b4576#32, 0x4da2bfeb#32), by simpa [oneHotDifference] using cell_25_06⟩
  · exact ⟨0x000000001d000000f79d8bd19989b5c2e0ee01746ffa05154886f88ce8cd0c90#256,
      (0x7c321184#32, 0x2bd2de3d#32), by simpa [oneHotDifference] using cell_25_07⟩
  · exact ⟨0x00000000c540ffff71c9693f14ae371bf3e2f7f83f60d257c43f66b71f95ace0#256,
      (0x1ba15c81#32, 0xb5db5ab5#32), by simpa [oneHotDifference] using cell_25_08⟩
  · exact ⟨0x000000006e000000803c374180dec440f07fb47483cfdf36c9415444dcb0f180#256,
      (0x74723a3f#32, 0x78666bc9#32), by simpa [oneHotDifference] using cell_25_09⟩
  · exact ⟨0x000000004d25ffff8ec75ad9cf33e5cae8daebd02292080728c61d3790a8aa3f#256,
      (0x122eec2f#32, 0x836bc4fb#32), by simpa [oneHotDifference] using cell_25_10⟩
  · exact ⟨0x000000004effffff0a2475401180041e065bbc0c017e8208b4f82deb0de623f8#256,
      (0x49de03a9#32, 0x5b52c3a7#32), by simpa [oneHotDifference] using cell_25_11⟩
  · exact ⟨0x00000000fb000000f8a873e3b0d8a8b8da6066bf881fbacae33210a0390e0080#256,
      (0xc84c97e8#32, 0xf7871091#32), by simpa [oneHotDifference] using cell_25_12⟩
  · exact ⟨0x0000000081000000a58fec22434701788c098cfdfd22f8ec769ee7e4127f1000#256,
      (0x96c1b6d5#32, 0x412224c0#32), by simpa [oneHotDifference] using cell_25_13⟩
  · exact ⟨0x0000000007e00000f37da81f3f9ec46072db84d6755c93bab05f72eef69d1000#256,
      (0x695c6eb1#32, 0x682fa86d#32), by simpa [oneHotDifference] using cell_25_14⟩
  · exact ⟨0x0000000027765ffd04d9a92543443e2409670e874cced7b6949a55973869a00d#256,
      (0x4db23792#32, 0xd8ae6d2b#32), by simpa [oneHotDifference] using cell_25_15⟩
  · exact ⟨0x00000000aa7fffff2fa15d24da1b5674737206b335f3ba32e8a943bfcf76ff89#256,
      (0xc8a13045#32, 0xc4494391#32), by simpa [oneHotDifference] using cell_25_16⟩
  · exact ⟨0x0000000097000000757f0368bc6e3f8682c7b702bb8d776e59b62cb4deee0000#256,
      (0xb91f31cf#32, 0x6b9d7ee4#32), by simpa [oneHotDifference] using cell_25_17⟩
  · exact ⟨0x0000000032000000b3119e40f2f7733b0fc933494ad19ee0fada652af5b1000d#256,
      (0x4d3d6a10#32, 0xee0d8e06#32), by simpa [oneHotDifference] using cell_25_18⟩
  · exact ⟨0x00000000a9800000fff5342003d5ffd21e9c7363260bf155d1441921663b0000#256,
      (0x10c54aed#32, 0xd0e8a591#32), by simpa [oneHotDifference] using cell_25_19⟩
  · exact ⟨0x00000000bb000000e6fce3fc13c52fdbcf2bf05d1b69816ab0c0b8f0c9f00000#256,
      (0x66462b16#32, 0x6b5f50cd#32), by simpa [oneHotDifference] using cell_25_20⟩
  · exact ⟨0x0000000039800000e3fbc5086a1cab07b77ebba405d48f2458ed24f095700000#256,
      (0x61635615#32, 0x2e9f4510#32), by simpa [oneHotDifference] using cell_25_21⟩
  · exact ⟨0x0000000091c00000377a7a942085082048ed4c19890bcb2a60218dd5052e9e0b#256,
      (0x1a5dcaf2#32, 0x75840bd4#32), by simpa [oneHotDifference] using cell_25_22⟩
  · exact ⟨0x00000000d5800000bc0c7e14706820f431f83f2dc1f820596f575a951e400000#256,
      (0xc24c6583#32, 0xe6f0be5a#32), by simpa [oneHotDifference] using cell_25_23⟩
  · exact ⟨0x00000000090000008e667d792835dc5d533f7102287f10cff641624107080000#256,
      (0x24ff1064#32, 0x2f74c094#32), by simpa [oneHotDifference] using cell_25_24⟩
  · exact ⟨0x00000000870000008d23c3fd2c02a664f42b3d18e13e5b221f47a3b867000000#256,
      (0xd2e4583b#32, 0xa120bb46#32), by simpa [oneHotDifference] using cell_25_25⟩
  · exact ⟨0x00000000b6000000d0d6931882922b8c87d642c112caffde78204be4fb838000#256,
      (0xa14290fb#32, 0x2e412762#32), by simpa [oneHotDifference] using cell_25_26⟩
  · exact ⟨0x00000000898000001fcf9d8d67e9b7f4c8cc9a2609137b12c7165d8c8a000300#256,
      (0xf7b961d7#32, 0x4ceb93cb#32), by simpa [oneHotDifference] using cell_25_27⟩
  · exact ⟨0x000000007400b000596d6b56d49ab25da53e153d5d98b5a5a164b49dd8220000#256,
      (0x009730f1#32, 0x29b4320e#32), by simpa [oneHotDifference] using cell_25_28⟩
  · exact ⟨0x000000004e000000e2b7b59f4b3c074c303f8477fd2717278ec5149cbb7cc000#256,
      (0xa5af438c#32, 0xdf83eb6e#32), by simpa [oneHotDifference] using cell_25_29⟩
  · exact ⟨0x000000006d033800a7cea1772dec0f46127781de34c58d927773c3d4c00ba900#256,
      (0x1451eedf#32, 0x20ae6659#32), by simpa [oneHotDifference] using cell_25_30⟩
  · exact ⟨0x000000005a00000095ab63446d350e0dc3e195e95a0729c217e664ef8655b379#256,
      (0x66ce1b23#32, 0x3fab919e#32), by simpa [oneHotDifference] using cell_25_31⟩

end Magma.DifanNineRoundPositiveRows
