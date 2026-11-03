module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row03Group00
public import Magma.Diffan.NineRoundPositiveRows.Row03Group01
public import Magma.Diffan.NineRoundPositiveRows.Row03Group02
public import Magma.Diffan.NineRoundPositiveRows.Row03Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 3. -/
theorem row03 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (3 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000a26ab7e37e94b8587b7835f93df9e54f2878d5ae05db03fa810478ff#256,
      (0xc40ad959#32, 0xf527c1f3#32), by simpa [oneHotDifference] using cell_03_00⟩
  · exact ⟨0x0000000022dd4c941fb0d904c5c5166d8f5d84ae3d8a773f19902e5bb1701362#256,
      (0x68fb9446#32, 0x295bf021#32), by simpa [oneHotDifference] using cell_03_01⟩
  · exact ⟨0x00000000568819d6b31b9e6ef57794800a3db45ba7654d52bce7cfdee0460cfa#256,
      (0x92864fb8#32, 0x72497c35#32), by simpa [oneHotDifference] using cell_03_02⟩
  · exact ⟨0x000000004bade6826a313c6ba269f176a434fdc1286b8344d79251e681a8db8c#256,
      (0x50e7c543#32, 0x6f73bec6#32), by simpa [oneHotDifference] using cell_03_03⟩
  · exact ⟨0x00000000d28964a8ce4e23140a2e72f07f365e6f9bdc4536b9d9aa4030648b50#256,
      (0x5f25d58f#32, 0x3d772c07#32), by simpa [oneHotDifference] using cell_03_04⟩
  · exact ⟨0x000000009f0c24130bb42122af400d042e45231eb26d5407683555cc63a8a260#256,
      (0x8bb279f0#32, 0x8228e331#32), by simpa [oneHotDifference] using cell_03_05⟩
  · exact ⟨0x00000000c1ae1a5a1d8b4cb49269bd5ba68d1cb31709a89dbc72e6d68ee5734e#256,
      (0x36a67a36#32, 0x9e8538fd#32), by simpa [oneHotDifference] using cell_03_06⟩
  · exact ⟨0x0000000057bef8fac40287bad7fe103f6b9c63db0d1ea5e0cb744793687b47c0#256,
      (0xbb4d7de0#32, 0x5c5aba1e#32), by simpa [oneHotDifference] using cell_03_07⟩
  · exact ⟨0x00000000041471193581767cea4f54a557aab8bb10f52cd144f882dfc0a986c0#256,
      (0x77bec3f6#32, 0xaeeb6857#32), by simpa [oneHotDifference] using cell_03_08⟩
  · exact ⟨0x000000005d8081aa3846e07a63fb361bbd9e74946f1d59c0a3eff268f779de47#256,
      (0xc10d7871#32, 0xd33a28ac#32), by simpa [oneHotDifference] using cell_03_09⟩
  · exact ⟨0x00000000a0a8eda4e8bab3fa0170b22f8fd2f63489e9effc6ca1a39acb2fc4f0#256,
      (0x394b899a#32, 0x15400477#32), by simpa [oneHotDifference] using cell_03_10⟩
  · exact ⟨0x00000000fb1572e59e7dfc07b17fceceaf2990930cb4918edc70adef915a5400#256,
      (0xfbcdb7c4#32, 0x5a093c1b#32), by simpa [oneHotDifference] using cell_03_11⟩
  · exact ⟨0x0000000010a574f9c46265e54b18ffab84620fe590d6087833c079727270c9cc#256,
      (0x602e9360#32, 0x4c12741d#32), by simpa [oneHotDifference] using cell_03_12⟩
  · exact ⟨0x000000005bae79c66f8c852d7485601e598d0c0c57c233b2ad4f7f77d97dcfff#256,
      (0xe5ff5b60#32, 0xad63c2d6#32), by simpa [oneHotDifference] using cell_03_13⟩
  · exact ⟨0x00000000dee96cb24c658a81a4a9d87071c8fb45b26d09b8a41c2ad00e3e2b00#256,
      (0x92975905#32, 0x809e8f37#32), by simpa [oneHotDifference] using cell_03_14⟩
  · exact ⟨0x0000000058f405ea185e2c7807f0fdddcf0c3dfb807b2187b6b7e9622aea80cc#256,
      (0xbe094f46#32, 0xad272f62#32), by simpa [oneHotDifference] using cell_03_15⟩
  · exact ⟨0x00000000b6ed273523efe60109aa8d6d20564d0edff73f9c488c63475a8b0ff8#256,
      (0x7de91388#32, 0xb5287ab7#32), by simpa [oneHotDifference] using cell_03_16⟩
  · exact ⟨0x00000000e222373910dbf9e695187bd0353e2c45d0f7c1f79ea0184884798000#256,
      (0xa711b612#32, 0x3d34762e#32), by simpa [oneHotDifference] using cell_03_17⟩
  · exact ⟨0x000000009762cc3d5d0619c539a65542ce486bdbcd0ea80815bff3148d03e0ec#256,
      (0x8616f67d#32, 0xe48149b9#32), by simpa [oneHotDifference] using cell_03_18⟩
  · exact ⟨0x00000000eec28b182a1b0ebb586c92e46dd8af1c319dc7b797c2bf7cb0b6ffbf#256,
      (0xc96bf1e3#32, 0xabd996dc#32), by simpa [oneHotDifference] using cell_03_19⟩
  · exact ⟨0x00000000a5ad0cc584cc956a9a813671293ab5d6138e37321008bc7e55cffaf2#256,
      (0xe4770519#32, 0xd32bbfc8#32), by simpa [oneHotDifference] using cell_03_20⟩
  · exact ⟨0x000000000005cefb92d985ddad30ead2a030adf439e4027094332e799f58f8ff#256,
      (0xf5f257c5#32, 0x308da1e0#32), by simpa [oneHotDifference] using cell_03_21⟩
  · exact ⟨0x0000000090f708d942d7a0c215481cc73fada5697268ff44c21a43c4d72fd0ff#256,
      (0x4eb24eaf#32, 0x7b63b76b#32), by simpa [oneHotDifference] using cell_03_22⟩
  · exact ⟨0x0000000064d560599dd1b0043f7985dc75600c5b277db39e1885659298ffb050#256,
      (0x7959125b#32, 0xe8d35bbf#32), by simpa [oneHotDifference] using cell_03_23⟩
  · exact ⟨0x0000000096b50b68d056c22f88c00127cc86ac05cb7d2e960cdb6cb280c18000#256,
      (0x4d23382d#32, 0xcf245737#32), by simpa [oneHotDifference] using cell_03_24⟩
  · exact ⟨0x00000000a540206d031b5630dd8772f520226e414a06150494f59107ee100008#256,
      (0xb869582d#32, 0x944546dc#32), by simpa [oneHotDifference] using cell_03_25⟩
  · exact ⟨0x000000007eb9b5b76d52543c999d6351628975fd913cc3c4b9b9d3eb939b6e80#256,
      (0x70e0cedb#32, 0xc2746bdc#32), by simpa [oneHotDifference] using cell_03_26⟩
  · exact ⟨0x000000005ecdbd6b3e23a2ee7ccf8353edc1849db564234861138f2819ffffa9#256,
      (0x3a9cc372#32, 0x770015dc#32), by simpa [oneHotDifference] using cell_03_27⟩
  · exact ⟨0x00000000776031c500e52253ea4dc32e94655961c52298ea7089cd34b87ffff8#256,
      (0x38ad9111#32, 0x23657ea6#32), by simpa [oneHotDifference] using cell_03_28⟩
  · exact ⟨0x00000000fcee030ae267ae4d41009843a0b32db98f3810330cb1cd46600cce1c#256,
      (0x783075b4#32, 0xf0681b3f#32), by simpa [oneHotDifference] using cell_03_29⟩
  · exact ⟨0x000000008619362ae8b8b5ee2c67c75f4a916a6983810ed2452cb5fe802218fc#256,
      (0x1df2e76b#32, 0x34eb1415#32), by simpa [oneHotDifference] using cell_03_30⟩
  · exact ⟨0x000000003c43d9d88122eeb7dd8034e51effb0028b238c5d85ae9ccf9a619f62#256,
      (0xd0dff5c6#32, 0x1c567cb4#32), by simpa [oneHotDifference] using cell_03_31⟩

end Magma.DiffanNineRoundPositiveRows
