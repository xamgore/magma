module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row27Group00
public import Magma.Diffan.NineRoundPositiveRows.Row27Group01
public import Magma.Diffan.NineRoundPositiveRows.Row27Group02
public import Magma.Diffan.NineRoundPositiveRows.Row27Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 27. -/
theorem row27 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (27 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000049f5d868c26ef12a335557c49f0cb8fa710f4f1b254fef95f6daafcb#256,
      (0xeb492ec1#32, 0xfd1e8459#32), by simpa [oneHotDifference] using cell_27_00⟩
  · exact ⟨0x0000000006f0effc5345ad272d432cf9a20bc309fa0c5286bf822b4d0a0a91ab#256,
      (0xd0ae47e8#32, 0x763f5ed0#32), by simpa [oneHotDifference] using cell_27_01⟩
  · exact ⟨0x00000000a700000000451a3b7481a48983d4aeeab33afac90fcce32ecc5b754b#256,
      (0x812d49d3#32, 0x8d7a39ff#32), by simpa [oneHotDifference] using cell_27_02⟩
  · exact ⟨0x00000000d96fba20d8bb08e1d691d1ab0d51ba2f8dfc49af569e8bee1eea1ab7#256,
      (0x72935674#32, 0x13c30e23#32), by simpa [oneHotDifference] using cell_27_03⟩
  · exact ⟨0x00000000356cc3ff420d99d9bb0e8ed34a3cd3ed19459fa4248169445bc84cf0#256,
      (0x72ecccd5#32, 0x25752cb2#32), by simpa [oneHotDifference] using cell_27_04⟩
  · exact ⟨0x00000000963984a961441428c8a0243437892a06c2e098401dc43d446873de5f#256,
      (0x7e4136fd#32, 0xe33c61e7#32), by simpa [oneHotDifference] using cell_27_05⟩
  · exact ⟨0x00000000d9007d800db85c1a0a05c0bd04109b038178cf9e0341115facb3314b#256,
      (0xbbed565b#32, 0xedaca994#32), by simpa [oneHotDifference] using cell_27_06⟩
  · exact ⟨0x00000000e959b83e228aa93ba2b03edc8248b5cd417d2d60530b7d452d8179db#256,
      (0xa4a05f6b#32, 0x039aa9c4#32), by simpa [oneHotDifference] using cell_27_07⟩
  · exact ⟨0x000000003bffffff532a3b11092e0eeae371ab1e85d9aebf6577f75aee3a32ff#256,
      (0x533a50b1#32, 0x5a7f7e73#32), by simpa [oneHotDifference] using cell_27_08⟩
  · exact ⟨0x0000000017f30bd6622ca9e9bb7690d1f1398e9dff5b23ae052bfe6d0bf87d00#256,
      (0x7016004c#32, 0xa44faad0#32), by simpa [oneHotDifference] using cell_27_09⟩
  · exact ⟨0x000000008531ff0fe5b689e7320e4064b7f26d28397472621e7725dc39225560#256,
      (0x5709cfa1#32, 0xb58ecc77#32), by simpa [oneHotDifference] using cell_27_10⟩
  · exact ⟨0x0000000066c00ffef60c1d3d7193e40064c00fcc5b46f45ff738f63aadef85c7#256,
      (0x4a3a83bd#32, 0x7b4a2c55#32), by simpa [oneHotDifference] using cell_27_11⟩
  · exact ⟨0x0000000038ffffff9f3d498ca099075c6da03bfd37726495b670e1749c68cfc0#256,
      (0x395059bf#32, 0xb2988b26#32), by simpa [oneHotDifference] using cell_27_12⟩
  · exact ⟨0x00000000c7000000d210f1d47532029eaadb7252d278904952db14cd6867f000#256,
      (0x331de829#32, 0x48323915#32), by simpa [oneHotDifference] using cell_27_13⟩
  · exact ⟨0x00000000e55fff8d676745d7f01f5be229c8eb1f28af7ef6d7cd4837d3275200#256,
      (0xce9d520e#32, 0xf8a73237#32), by simpa [oneHotDifference] using cell_27_14⟩
  · exact ⟨0x00000000f5f800c265d0c2635dc84c43e00f5713f03b8cecbfb9105603a04315#256,
      (0xe0f3a901#32, 0x183cbebe#32), by simpa [oneHotDifference] using cell_27_15⟩
  · exact ⟨0x00000000b50000005ee3911a05f3f3a0a9014dfc39eebe905f654914fecac0ab#256,
      (0x8307d954#32, 0x2228fc69#32), by simpa [oneHotDifference] using cell_27_16⟩
  · exact ⟨0x00000000a0fefcfe05c5b90368005b44f866e7c18c09c79add0178d84a5cf96d#256,
      (0x26f95986#32, 0xe1a4278d#32), by simpa [oneHotDifference] using cell_27_17⟩
  · exact ⟨0x00000000e5000000e1ae31b5414828087a2b03cf96e6f114c6e229794ed20000#256,
      (0x0e2192b9#32, 0xae6387ff#32), by simpa [oneHotDifference] using cell_27_18⟩
  · exact ⟨0x000000005a0000007018b8955b1834dd25b557170c427e1dd9308a6e424a5000#256,
      (0xa0414d7e#32, 0x540ac0d5#32), by simpa [oneHotDifference] using cell_27_19⟩
  · exact ⟨0x00000000e8000000792ca3ea886ecba8fa0731bbd0b9730966c725d0d5cf80a0#256,
      (0x801fbbc0#32, 0x97809abf#32), by simpa [oneHotDifference] using cell_27_20⟩
  · exact ⟨0x000000001d0001000c1018c92fb8396b230c1d254b061475c44ff28bf3de0000#256,
      (0x1b92011a#32, 0x8f0e803e#32), by simpa [oneHotDifference] using cell_27_21⟩
  · exact ⟨0x000000008a0000004930e2c8268510e4dfcf1d2c0ea1b018acce855b5ae00000#256,
      (0x8442b075#32, 0x83b202c4#32), by simpa [oneHotDifference] using cell_27_22⟩
  · exact ⟨0x0000000093000000a6b90e6e7bcfb067b78e942a3869efa3ef6e0ce3f5c1dc00#256,
      (0x2fdff2e8#32, 0xe52fbd60#32), by simpa [oneHotDifference] using cell_27_23⟩
  · exact ⟨0x00000000970000000c5f1a619bd8b1a889da8ca55fa3ea4153e79c039ac06030#256,
      (0x571af11e#32, 0xbd9c7afe#32), by simpa [oneHotDifference] using cell_27_24⟩
  · exact ⟨0x0000000087c000008f4c12a3dc8501a7e90c19fedf8b03ac7c28332de5f80000#256,
      (0x2785c90f#32, 0x1909f79c#32), by simpa [oneHotDifference] using cell_27_25⟩
  · exact ⟨0x00000000fa00000035e423e989069dfe1731b49d51a8ede7b514494949007c00#256,
      (0xd106920b#32, 0x1f903cea#32), by simpa [oneHotDifference] using cell_27_26⟩
  · exact ⟨0x0000000051000000d167943e985303f8501cc351461f4b1fe3826dd813e00000#256,
      (0x6dd067f3#32, 0x31535cb4#32), by simpa [oneHotDifference] using cell_27_27⟩
  · exact ⟨0x0000000029fc0000f09babf5cc4e062b71915dfcee5efe599c3ac97ef57b0b00#256,
      (0x5bc83ea1#32, 0x5536bdfc#32), by simpa [oneHotDifference] using cell_27_28⟩
  · exact ⟨0x0000000058900000f05c2d51efeeb491064371ce1d049210d09435f45c0b000d#256,
      (0xee8d7e59#32, 0x196c58a2#32), by simpa [oneHotDifference] using cell_27_29⟩
  · exact ⟨0x000000004d3800008e068cad40bdd048e894d4f670838448d1f6c0d1d024008c#256,
      (0x55af0139#32, 0xd6f8d446#32), by simpa [oneHotDifference] using cell_27_30⟩
  · exact ⟨0x00000000f90be04004d0eaca6bee23c214a3846f3e7fe682606a83f0882aa6a6#256,
      (0xf5ad8cbd#32, 0x7554c2ae#32), by simpa [oneHotDifference] using cell_27_31⟩

end Magma.DiffanNineRoundPositiveRows
