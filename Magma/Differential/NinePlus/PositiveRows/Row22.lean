module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row22Group00
public import Magma.Differential.NinePlus.PositiveRows.Row22Group01
public import Magma.Differential.NinePlus.PositiveRows.Row22Group02
public import Magma.Differential.NinePlus.PositiveRows.Row22Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 22. -/
theorem row22 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (22 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000acc264fd3dbdc4bc1ff5a28e1fc3a2f285ed35680ba87c91adfd3691#256,
      (0xa525f364#32, 0xf4ce0700#32), by simpa [oneHotDifference] using cell_22_00⟩
  · exact ⟨0x00000000013fffffda354c1a3759be841dae29d94de90872f2bd9fcde8773f49#256,
      (0x4040d1ea#32, 0xb7924388#32), by simpa [oneHotDifference] using cell_22_01⟩
  · exact ⟨0x0000000062977f3cf888750016b2904b5c13f663ad0313770606898e2df183b4#256,
      (0xf5086440#32, 0xcb2c9ac9#32), by simpa [oneHotDifference] using cell_22_02⟩
  · exact ⟨0x0000000077dfffffba61eb673c6801bbc6ea367c0fbaf6ce25dd654b65db2823#256,
      (0x34dc5048#32, 0xe4e1ed74#32), by simpa [oneHotDifference] using cell_22_03⟩
  · exact ⟨0x00000000872c6cfe11363be7818a9e2c218446ed7cfb7f401064206ef304e411#256,
      (0x35fffdeb#32, 0x3cd2a335#32), by simpa [oneHotDifference] using cell_22_04⟩
  · exact ⟨0x000000003830fffdfefa110b871b97fa669d1adbab7fbdf1529cc23423002d58#256,
      (0xc600fe18#32, 0xbaa94a0f#32), by simpa [oneHotDifference] using cell_22_05⟩
  · exact ⟨0x0000000053b13fdb69bd42e1a2c03c2057bd2f9907a46ddbda069f1f7bd10470#256,
      (0x2ef6a735#32, 0x1254b618#32), by simpa [oneHotDifference] using cell_22_06⟩
  · exact ⟨0x00000000bc1000007d32a95a5416cf022fe6a2c072009c62d379ea7b1c1437a0#256,
      (0x06a19df9#32, 0xf458a4c6#32), by simpa [oneHotDifference] using cell_22_07⟩
  · exact ⟨0x00000000225c2ffeb563313acb69f7623519be6a2e6ee87c77b1de32843924ff#256,
      (0xbf577d1d#32, 0x5f73b64b#32), by simpa [oneHotDifference] using cell_22_08⟩
  · exact ⟨0x000000002cbf0ffff12f451bd6da63397dcfecc1190b7c0a02b7748a9785c5b8#256,
      (0x71122db0#32, 0x459f5302#32), by simpa [oneHotDifference] using cell_22_09⟩
  · exact ⟨0x0000000075deffffa47f7bc9feab6193163373f6204d48b0763fd9c35f0918f3#256,
      (0xbec31e5a#32, 0xe337642b#32), by simpa [oneHotDifference] using cell_22_10⟩
  · exact ⟨0x00000000b53000004096eddbb80adcad6a4ea3e0ce84a98ee0adb33246489500#256,
      (0xc3ba3613#32, 0x405c22d5#32), by simpa [oneHotDifference] using cell_22_11⟩
  · exact ⟨0x000000000fcfffff822724e2534cec33dafff88d7da7d890ea15a612130629ff#256,
      (0x6df8ac9f#32, 0x568cfcdb#32), by simpa [oneHotDifference] using cell_22_12⟩
  · exact ⟨0x00000000aba59f4d73ec9ec037675f90a00ff895f0133e9f6156a9c8f6b41c00#256,
      (0xe357e0a0#32, 0x498bd5ff#32), by simpa [oneHotDifference] using cell_22_13⟩
  · exact ⟨0x0000000025ad26f9389393ec6d60b69561027540b18407546ee164c16b184900#256,
      (0x7c9aca34#32, 0xbfbf429e#32), by simpa [oneHotDifference] using cell_22_14⟩
  · exact ⟨0x0000000060b8d54ee1dcb05c4ba4b6d3182ae234e64ef57fec69530c9ec67570#256,
      (0x42cb8490#32, 0xdfdc86d1#32), by simpa [oneHotDifference] using cell_22_15⟩
  · exact ⟨0x00000000af100000688302790b95a7d2f7337d42333c70ed39e3487644468000#256,
      (0x3ebae619#32, 0x695509b3#32), by simpa [oneHotDifference] using cell_22_16⟩
  · exact ⟨0x00000000dec1ffff65c461ceed741bbb189723e433f728fcab5c4ac64302d800#256,
      (0x8474a2d4#32, 0xaff3a2e8#32), by simpa [oneHotDifference] using cell_22_17⟩
  · exact ⟨0x00000000cfd71cd41dc54ca0f4faef4ca93515ebce8f74e42e65636531939c00#256,
      (0x86f9cb7a#32, 0x6dfd4bad#32), by simpa [oneHotDifference] using cell_22_18⟩
  · exact ⟨0x0000000086d0807f4d96601f7d1b2f5b20329c0b3c1a5adc13972ab45d9ab7f8#256,
      (0x59974c43#32, 0x8539503b#32), by simpa [oneHotDifference] using cell_22_19⟩
  · exact ⟨0x00000000a3e00000f82195de9b2f1b4c8e2eaef0962cf8fbba02e89d0e5b0000#256,
      (0xe6f4e844#32, 0x83b8eaaf#32), by simpa [oneHotDifference] using cell_22_20⟩
  · exact ⟨0x0000000039600000da5c802275547a815493179f099b3665f623429873d80000#256,
      (0x33674d86#32, 0xa76b1d9d#32), by simpa [oneHotDifference] using cell_22_21⟩
  · exact ⟨0x0000000011be0000db1f71c17b271110939e2907bb860c2c249806780b200000#256,
      (0x26cbfbdc#32, 0x69273238#32), by simpa [oneHotDifference] using cell_22_22⟩
  · exact ⟨0x000000003e3af5ed056562687a62aa728405f0f6b24af16bed1ab25d7d391f46#256,
      (0xfd9e07eb#32, 0x98d515a5#32), by simpa [oneHotDifference] using cell_22_23⟩
  · exact ⟨0x00000000f47800002571462a77e6863a02daf6ad8b3a43208c61d22daac00080#256,
      (0xf5a55544#32, 0xd84f4930#32), by simpa [oneHotDifference] using cell_22_24⟩
  · exact ⟨0x000000002cb000005d62bb356a16f99e58594a5d898c6a9e2710b7880638b000#256,
      (0xf1cf5589#32, 0xd45eb4c5#32), by simpa [oneHotDifference] using cell_22_25⟩
  · exact ⟨0x00000000ea100000a004ac8dba153ac1ebe65c64dd0abac8145355e7d6000000#256,
      (0xe82178a0#32, 0x32daf4be#32), by simpa [oneHotDifference] using cell_22_26⟩
  · exact ⟨0x000000009a100000ae54755249699949f0e00d30f5878002786cae2f1bc00000#256,
      (0xb1fc8413#32, 0xe2bb1f19#32), by simpa [oneHotDifference] using cell_22_27⟩
  · exact ⟨0x00000000536000009ac33c13dbcc6b085084090c67779bd17e4064f120000008#256,
      (0xa720cb57#32, 0xf611878d#32), by simpa [oneHotDifference] using cell_22_28⟩
  · exact ⟨0x000000000ad00000076a29698ce167f4e9d818c08d84cec96e1b72b8d0000000#256,
      (0x58a23b03#32, 0xbd60fb98#32), by simpa [oneHotDifference] using cell_22_29⟩
  · exact ⟨0x0000000053600000c709a90afd4d1a65920989d438e98d6dca64ca90bc773d00#256,
      (0x65e5cc0f#32, 0xb20a4eef#32), by simpa [oneHotDifference] using cell_22_30⟩
  · exact ⟨0x00000000a0700000520c33712a2c6f16a3870955bdaa9ee1833066a0582d2c27#256,
      (0x147f89bb#32, 0x7eaa8596#32), by simpa [oneHotDifference] using cell_22_31⟩

end Magma.DiffanNineRoundPositiveRows
