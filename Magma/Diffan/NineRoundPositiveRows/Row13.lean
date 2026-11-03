module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row13Group00
public import Magma.Diffan.NineRoundPositiveRows.Row13Group01
public import Magma.Diffan.NineRoundPositiveRows.Row13Group02
public import Magma.Diffan.NineRoundPositiveRows.Row13Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 13. -/
theorem row13 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (13 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000081cb000eadf0afeae43323337247662fa41b77d9b7bfe28e8af927b#256,
      (0x381fbb0a#32, 0x20e96546#32), by simpa [oneHotDifference] using cell_13_00⟩
  · exact ⟨0x00000000ce5330056bc393e56d014bac23f684b461873aa0707cc3e1c123d04e#256,
      (0xb40ed306#32, 0xc1085cab#32), by simpa [oneHotDifference] using cell_13_01⟩
  · exact ⟨0x00000000f95bd0000af8be8e83168d0dc470d7945812b62c94ea678bc7a826b9#256,
      (0x6bfb44b2#32, 0x9a693998#32), by simpa [oneHotDifference] using cell_13_02⟩
  · exact ⟨0x00000000a464dfff6984ceab9cbcff37e4b50d1c955888ae90c40ad2d61be287#256,
      (0x593c2e13#32, 0x1b47cf9b#32), by simpa [oneHotDifference] using cell_13_03⟩
  · exact ⟨0x00000000bf61a0ff9b4769955b33e23c86d6c3383b391e88cf495ecf3b71b310#256,
      (0x6b5a1652#32, 0x0cccc61e#32), by simpa [oneHotDifference] using cell_13_04⟩
  · exact ⟨0x00000000ba6a5b6c8c11c2dc6562cbdcbc4c122d4225f8ae7243a5eab7a42ea0#256,
      (0xb1916b6f#32, 0x784b9f49#32), by simpa [oneHotDifference] using cell_13_05⟩
  · exact ⟨0x00000000717561ff0e0579de2c24251784e6f4015dc65adf2044c18476529a50#256,
      (0x7b84f9dc#32, 0xaa66b578#32), by simpa [oneHotDifference] using cell_13_06⟩
  · exact ⟨0x000000008f9a0cd427b1ea4218e94597156266293300f4f859e2be2fa6499245#256,
      (0x06f2b0d6#32, 0x218e4499#32), by simpa [oneHotDifference] using cell_13_07⟩
  · exact ⟨0x000000004a889f00b44d8b8212ff1084be6bfd081914c48378a0aa627b843708#256,
      (0xd207ab44#32, 0x5ec3d88e#32), by simpa [oneHotDifference] using cell_13_08⟩
  · exact ⟨0x00000000d48c27ffd44397dc131ac08cef3b157f4b1dfc445ba8d200c60e76d0#256,
      (0x05877785#32, 0x112e4c43#32), by simpa [oneHotDifference] using cell_13_09⟩
  · exact ⟨0x00000000702d5fff9ced47388175348a7307a7d896c5824cd82cb775f8f480ff#256,
      (0xac340c6a#32, 0x87ecbcd2#32), by simpa [oneHotDifference] using cell_13_10⟩
  · exact ⟨0x00000000fc65e1ba2ae032e5bb7f3c014825d6ff272ef6cb4924bce3fd54a287#256,
      (0x8981cbe6#32, 0xf1ec71b0#32), by simpa [oneHotDifference] using cell_13_11⟩
  · exact ⟨0x00000000ab73f389afdd09248e0a9908e0495c8d2aa23fe15d3eb1c863270fd0#256,
      (0x665c418c#32, 0xfd0adbea#32), by simpa [oneHotDifference] using cell_13_12⟩
  · exact ⟨0x00000000c7e21ffffdbe1cdec4c3b6adbf0986a21fc58261336fb0cf0305107d#256,
      (0x4b5fe9c7#32, 0xf11473af#32), by simpa [oneHotDifference] using cell_13_13⟩
  · exact ⟨0x000000001c7f27fe1751aa3af86861cb3a8a9ae7c7728ba408a5fe6cf280b0f8#256,
      (0x8ea41ace#32, 0x591e9b4a#32), by simpa [oneHotDifference] using cell_13_14⟩
  · exact ⟨0x0000000009f34fffaa69ec759fd761c2789b3c96e5c5c79b8e3aee8fdb673f8f#256,
      (0xe8428fc9#32, 0x11c9ffa5#32), by simpa [oneHotDifference] using cell_13_15⟩
  · exact ⟨0x00000000d2d5afff067c675017d2b6b4a616da5c3880b39370631e4cbafcd00a#256,
      (0x389e3736#32, 0x473cce1e#32), by simpa [oneHotDifference] using cell_13_16⟩
  · exact ⟨0x00000000a03e0fffe042d27007b170921b0e6d737e36dae72797b98addce01c2#256,
      (0xe5710cb4#32, 0x97d7be86#32), by simpa [oneHotDifference] using cell_13_17⟩
  · exact ⟨0x000000004eb32380e44f446e9eb36fbc567960da4174613b243630e04ba47193#256,
      (0x0dad09fb#32, 0xf21a2638#32), by simpa [oneHotDifference] using cell_13_18⟩
  · exact ⟨0x00000000f5a7d800bb88e92d5b6fc18197b38eab82604255f9e8c3c2e0b70000#256,
      (0xe5fe3e2c#32, 0xebc26b7c#32), by simpa [oneHotDifference] using cell_13_19⟩
  · exact ⟨0x000000002540dfffd4a690707cfe14095773f272a9474d369dd20751acb63ea2#256,
      (0x0113b5d9#32, 0x8e478241#32), by simpa [oneHotDifference] using cell_13_20⟩
  · exact ⟨0x0000000090f51e003fac0fff53a15e46f2a33900b173a12c7eb3f045eae00000#256,
      (0x81c35f67#32, 0x6c8a673b#32), by simpa [oneHotDifference] using cell_13_21⟩
  · exact ⟨0x000000005bf68fffc2ba6f1010e21decab025a456c97d2002c03ed4323b05b2d#256,
      (0xc41fb65c#32, 0x1edfd4d9#32), by simpa [oneHotDifference] using cell_13_22⟩
  · exact ⟨0x000000007c495ffe7e35f7d00250ab65e64c46ff2c73685d92c65386026bbe00#256,
      (0xcc17e75a#32, 0xff11bb20#32), by simpa [oneHotDifference] using cell_13_23⟩
  · exact ⟨0x000000005c878fff80fb36640b3b80efabb275342256c53f48834946a0091d0d#256,
      (0x5981a77d#32, 0xfd1cb538#32), by simpa [oneHotDifference] using cell_13_24⟩
  · exact ⟨0x000000002cc70fff61282c18729e34430227ce6fac808ffae85734ab96ffff81#256,
      (0x4592a8fa#32, 0xf31642a8#32), by simpa [oneHotDifference] using cell_13_25⟩
  · exact ⟨0x000000009b1aa1bfd49b99bcb396ef4a830ea38c3856d3183eb765faf521f0a2#256,
      (0xf3e0562a#32, 0x12a3df5f#32), by simpa [oneHotDifference] using cell_13_26⟩
  · exact ⟨0x000000002544afffd0e08fd822002a2683c7073ba92c1554960efcccd39e7d4f#256,
      (0xe8bb42ef#32, 0x1ae85fef#32), by simpa [oneHotDifference] using cell_13_27⟩
  · exact ⟨0x00000000880edfffb3c6f122e023d33e33eb167c4e5e2817886aa3fd9f97f8ff#256,
      (0xb560c859#32, 0xef8f5f6e#32), by simpa [oneHotDifference] using cell_13_28⟩
  · exact ⟨0x000000005f262ffe8aa910490eb7a97d452a83d44e0183bbd7d01cf4d0179009#256,
      (0x622ad458#32, 0xc57cf80d#32), by simpa [oneHotDifference] using cell_13_29⟩
  · exact ⟨0x000000003ebad000889628f6a1f84f6654570a31a46a177bfda452d050001800#256,
      (0xd5d2b28f#32, 0x9768e4f5#32), by simpa [oneHotDifference] using cell_13_30⟩
  · exact ⟨0x00000000082befff46deb4b31aea2a9ed4fb05fb5ec7d0f21ed61e13a54c76fe#256,
      (0x4c9a871d#32, 0xf851addf#32), by simpa [oneHotDifference] using cell_13_31⟩

end Magma.DiffanNineRoundPositiveRows
