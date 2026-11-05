module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row26Group00
public import Magma.Differential.NinePlus.PositiveRows.Row26Group01
public import Magma.Differential.NinePlus.PositiveRows.Row26Group02
public import Magma.Differential.NinePlus.PositiveRows.Row26Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 26. -/
theorem row26 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (26 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000004a00000096efb489a002cbf7b06b0cac29c27b7b4b2fa56c2d1d6943#256,
      (0x4a4d7b3e#32, 0xfce2eb3e#32), by simpa [oneHotDifference] using cell_26_00⟩
  · exact ⟨0x00000000214fffffda4324154d4408244543700ed06f989721738be4005f5f1e#256,
      (0xb9af8091#32, 0xcd5d52db#32), by simpa [oneHotDifference] using cell_26_01⟩
  · exact ⟨0x00000000db8fd5c409e1983eaa05c0be561127827ce5614352bbfe5cf31dad25#256,
      (0xc8f39eb9#32, 0x9eae24b8#32), by simpa [oneHotDifference] using cell_26_02⟩
  · exact ⟨0x00000000aca240089609ee8b7f08e74c26141b6011cfa40334ae3079580d9fa5#256,
      (0x596071c2#32, 0x84d1aa57#32), by simpa [oneHotDifference] using cell_26_03⟩
  · exact ⟨0x00000000d90d0500061e1c36a806cc177f505507b1db911d38ae69d49049ef13#256,
      (0x5edbffb3#32, 0x777aaa84#32), by simpa [oneHotDifference] using cell_26_04⟩
  · exact ⟨0x0000000078213c6845e745d3e8ff1c4fae7da4bb9716349e7053c5a6fefadb30#256,
      (0x2b74649a#32, 0x26773265#32), by simpa [oneHotDifference] using cell_26_05⟩
  · exact ⟨0x00000000be8307fd1abc11e58499c44eaad08989fc58c75faf34b18618d14cda#256,
      (0x0761fd96#32, 0x29f87a1d#32), by simpa [oneHotDifference] using cell_26_06⟩
  · exact ⟨0x00000000132fffff34ee9c9857129a00e1478b7042c45e37be844858214a705f#256,
      (0x053997a1#32, 0x64d1e8b8#32), by simpa [oneHotDifference] using cell_26_07⟩
  · exact ⟨0x00000000554f5fffe8f53bfa7deceead811e52da072cd614f600659920a65c80#256,
      (0x1f4503bf#32, 0x29fdb8cd#32), by simpa [oneHotDifference] using cell_26_08⟩
  · exact ⟨0x000000002d000000a93fd970c00ef0d8fa04aff90d9717dbd2afc42dd9727200#256,
      (0x6836565f#32, 0x11ba298c#32), by simpa [oneHotDifference] using cell_26_09⟩
  · exact ⟨0x00000000d1ffffff1dc673bc14c9f604ccebffe6c4497fd2ebbfde2c8e882d98#256,
      (0xf1403d13#32, 0xfb9a80aa#32), by simpa [oneHotDifference] using cell_26_10⟩
  · exact ⟨0x00000000b66fffffcb1fd910eeb88e153b802042c07adb83431e7eacba6f2e7c#256,
      (0x1ed6e833#32, 0x60f6133d#32), by simpa [oneHotDifference] using cell_26_11⟩
  · exact ⟨0x0000000082fcffff105e4d15bd2b6219263d6bb92cd38d39994ea3d6ae9f2c00#256,
      (0xafb4efb0#32, 0xe20893ed#32), by simpa [oneHotDifference] using cell_26_12⟩
  · exact ⟨0x000000000f000000f933c640adf98988c3d5f7135482d49cff570688c0ec9900#256,
      (0xb74e0da8#32, 0x366d6422#32), by simpa [oneHotDifference] using cell_26_13⟩
  · exact ⟨0x00000000bd000000c0f1dca392682d6f4d1c0457f1a6b548ed1114e78b94d000#256,
      (0xab7136a7#32, 0x0cdad8f2#32), by simpa [oneHotDifference] using cell_26_14⟩
  · exact ⟨0x00000000c2f439fadd99aa1422ffa709219e333b096df349357db503ce852200#256,
      (0x43f1cc6d#32, 0x8a97b718#32), by simpa [oneHotDifference] using cell_26_15⟩
  · exact ⟨0x00000000030000001e324528368ecfa0d117ed59f410f513b59875bc88230000#256,
      (0x0f7bfe24#32, 0x9e464ca2#32), by simpa [oneHotDifference] using cell_26_16⟩
  · exact ⟨0x000000005b845500b5f2c252ee43ebe9f6d0267ddff67fc062c989e5560e0003#256,
      (0x1734e3c5#32, 0xd2238dc5#32), by simpa [oneHotDifference] using cell_26_17⟩
  · exact ⟨0x000000000e000000e0ef1bac3fe2a47bef51f23ed48695dc7c1f5d6e82bb0000#256,
      (0xe6f7a628#32, 0x5c754d66#32), by simpa [oneHotDifference] using cell_26_18⟩
  · exact ⟨0x000000004f000000b363f29dfff0891fb872ddf5b6978dbd8c4939e3e6d70000#256,
      (0x07b62e2b#32, 0xdb8d7202#32), by simpa [oneHotDifference] using cell_26_19⟩
  · exact ⟨0x00000000ca0000005b794d3b8d97c1c7b86d804528645939e805abed0fb00000#256,
      (0x736a87c5#32, 0xd39ecd03#32), by simpa [oneHotDifference] using cell_26_20⟩
  · exact ⟨0x00000000d87507763a3f8468723b58507291abf8b4bc39de0829239f39601000#256,
      (0x2c002a47#32, 0x35e78216#32), by simpa [oneHotDifference] using cell_26_21⟩
  · exact ⟨0x00000000c3c00000df99391eba169fd3be880cdaa78a7447384a653c95304000#256,
      (0xfe0ea0fb#32, 0x13239362#32), by simpa [oneHotDifference] using cell_26_22⟩
  · exact ⟨0x0000000081000000a70aed886f7e1c3c0a4ded175f5566b78bc89d396f800000#256,
      (0x34b9802d#32, 0xc9e56ea9#32), by simpa [oneHotDifference] using cell_26_23⟩
  · exact ⟨0x00000000fe0000002fd11c6c9c6233bf0c65a6a4f228de443ec372c07f008000#256,
      (0x6eea9c63#32, 0xd172b972#32), by simpa [oneHotDifference] using cell_26_24⟩
  · exact ⟨0x00000000d10000006f643358499dc3e69aff46113fe0b70122d20358a3f80000#256,
      (0x1047e94e#32, 0x9a7cd9ef#32), by simpa [oneHotDifference] using cell_26_25⟩
  · exact ⟨0x00000000d30f800021de0e08d506ddcb3630e1b8c20727a3884e933dd9c97c00#256,
      (0x45f66c4b#32, 0xc1d21a6c#32), by simpa [oneHotDifference] using cell_26_26⟩
  · exact ⟨0x00000000edd00000b90dfc99b0fe99ab5a68cc5d237650bf65cbc1db4bf2400c#256,
      (0x2103837a#32, 0x8d9b47b2#32), by simpa [oneHotDifference] using cell_26_27⟩
  · exact ⟨0x00000000127a00005f25472b097efab5fa2a4e60bf00676c10f5d3abb00a0880#256,
      (0x0a3eb417#32, 0xdd661ae7#32), by simpa [oneHotDifference] using cell_26_28⟩
  · exact ⟨0x00000000ccffc000fbe6dc470f0ba0ce2307d81fa4a30d9d9fef597e2ffff8f0#256,
      (0x620a50e8#32, 0x22fed1ad#32), by simpa [oneHotDifference] using cell_26_29⟩
  · exact ⟨0x00000000641f80005daf08632f794f6174d8e1f2c4172034ae22c11770d71800#256,
      (0x7f7ad566#32, 0x56f88a19#32), by simpa [oneHotDifference] using cell_26_30⟩
  · exact ⟨0x00000000a600000047c935bada053c2092bc40481ed6eba70be395a020e77a02#256,
      (0x404da9f0#32, 0xed57ef2a#32), by simpa [oneHotDifference] using cell_26_31⟩

end Magma.DiffanNineRoundPositiveRows
