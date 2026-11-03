module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row18Group00
public import Magma.Diffan.NineRoundPositiveRows.Row18Group01
public import Magma.Diffan.NineRoundPositiveRows.Row18Group02
public import Magma.Diffan.NineRoundPositiveRows.Row18Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 18. -/
theorem row18 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (18 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000ada1ffff58ab8d57e4637dff8e44dc7d91f749e037e5a15ec7f30569#256,
      (0x2d955dd1#32, 0xda816d7a#32), by simpa [oneHotDifference] using cell_18_00⟩
  · exact ⟨0x0000000008d2ffff13ceb1bfd5b3489f6c5f83adbe03cb9928510af5bce79296#256,
      (0x92e129cf#32, 0xfe4ffd8e#32), by simpa [oneHotDifference] using cell_18_01⟩
  · exact ⟨0x00000000e98c3ffb0e6c8c8d283ef14371487ffbf233c43e6a102d0de2006395#256,
      (0x9827b990#32, 0xf64c3c2b#32), by simpa [oneHotDifference] using cell_18_02⟩
  · exact ⟨0x000000009902ffff904201d3ee43eb98c5b4248c56765cf7aa28abda30357123#256,
      (0xcfaa2aa6#32, 0x1d853bec#32), by simpa [oneHotDifference] using cell_18_03⟩
  · exact ⟨0x000000004cabffffc786a9e555d9eb1cbcdb001888e64d7a5878aa7665ba3113#256,
      (0x7149a5fe#32, 0x57669049#32), by simpa [oneHotDifference] using cell_18_04⟩
  · exact ⟨0x000000001a62ec5c83dfde6a9404557cd8e07b184e0472f1268027627479e15c#256,
      (0x438b50b3#32, 0xc96e047c#32), by simpa [oneHotDifference] using cell_18_05⟩
  · exact ⟨0x000000004b4c07f8444a0cb46a22cdc34b8fa2da39f17657965704696f2450aa#256,
      (0xc5c16ce7#32, 0xea5828bd#32), by simpa [oneHotDifference] using cell_18_06⟩
  · exact ⟨0x000000004f9a7ffff15ce5458f6512aa068b35348aaf1dd9c5fb049ca8b9ca60#256,
      (0xa9c17986#32, 0x87832e44#32), by simpa [oneHotDifference] using cell_18_07⟩
  · exact ⟨0x00000000c74500002f69d95295ac76f1f6c718fd112494059308eecc36246f00#256,
      (0xf65c7cd8#32, 0xbf8c0b15#32), by simpa [oneHotDifference] using cell_18_08⟩
  · exact ⟨0x0000000057b4f96d8dfd4b57ec55d60e217606925096d0a4843f5b1a3753b290#256,
      (0x33406008#32, 0x3edd795d#32), by simpa [oneHotDifference] using cell_18_09⟩
  · exact ⟨0x00000000a1d30000df721f4b29a76aa8d4f1fb73ef904636211bf3aa72560a00#256,
      (0x012fd7aa#32, 0x9e41dfe1#32), by simpa [oneHotDifference] using cell_18_10⟩
  · exact ⟨0x00000000f28cfd84ae0687e726c20275eae2673d1abd041f4aacab5027e4dc80#256,
      (0xb68663c0#32, 0x20e34609#32), by simpa [oneHotDifference] using cell_18_11⟩
  · exact ⟨0x000000000d4b8e822b641f36d2f8bb56cd47a70398ec2cb9b4da427dc597eca2#256,
      (0x89b4bfc8#32, 0x3442fb39#32), by simpa [oneHotDifference] using cell_18_12⟩
  · exact ⟨0x00000000f7f3ffff4423cd81eb76930701661d9e73f65178ffae738bea334fff#256,
      (0x6fc93c6d#32, 0x850d6eba#32), by simpa [oneHotDifference] using cell_18_13⟩
  · exact ⟨0x00000000fbadf3fa6115edae6e1d3c7fc8de81a280b3758bc7b3925a0d02907e#256,
      (0x6b194991#32, 0x034cdd59#32), by simpa [oneHotDifference] using cell_18_14⟩
  · exact ⟨0x000000000f543f625f12c350c2de3de13e467b18f84e1f1d25148d90b0405fa1#256,
      (0x41558503#32, 0xeee2c547#32), by simpa [oneHotDifference] using cell_18_15⟩
  · exact ⟨0x000000002a6600005246a1b5cd3d46d9edbbf9c24071013d018bd1fcdaca8000#256,
      (0x25d527dd#32, 0xc6a49d25#32), by simpa [oneHotDifference] using cell_18_16⟩
  · exact ⟨0x0000000056647fff72c8db35fe7b7d23cbfd82398df38dcc514174addc5b3cd0#256,
      (0x1ff43392#32, 0xbf151917#32), by simpa [oneHotDifference] using cell_18_17⟩
  · exact ⟨0x000000002021ffffa8bccd90ff564bdbe6203b604dea192a0dab9d392a81ff8f#256,
      (0xfda4f65b#32, 0x8af45504#32), by simpa [oneHotDifference] using cell_18_18⟩
  · exact ⟨0x00000000467b0886a553d496216284c355141dc655c93ba2053a64de3ad9fd85#256,
      (0x4e71a8c8#32, 0x35c8ef9d#32), by simpa [oneHotDifference] using cell_18_19⟩
  · exact ⟨0x000000005ca2ffff6f8d76743b53f28d4545268d78e27e3da67392f50ffcfc30#256,
      (0x166a52ed#32, 0x68d65e48#32), by simpa [oneHotDifference] using cell_18_20⟩
  · exact ⟨0x000000000daa0000cd7b6d0eb58837dfb5157914c3cce1b5377cbd9d244dfe09#256,
      (0x6b7a8e50#32, 0x090c2229#32), by simpa [oneHotDifference] using cell_18_21⟩
  · exact ⟨0x000000003beb7e539082817a31b879f3eb2c0092161f5a58152d91d6b5c003c0#256,
      (0x8c41f8b2#32, 0x519adeb8#32), by simpa [oneHotDifference] using cell_18_22⟩
  · exact ⟨0x00000000a181ffff9d1e0fe3eff417b50c973de9fe4616e7abff99491e98a8c0#256,
      (0x4f78f45f#32, 0x89c4d041#32), by simpa [oneHotDifference] using cell_18_23⟩
  · exact ⟨0x0000000070b70010af3171e833e7628ac0769552dae9663d0692548a44e80000#256,
      (0xfbde4ab0#32, 0x8c3eb4ac#32), by simpa [oneHotDifference] using cell_18_24⟩
  · exact ⟨0x0000000003e20000b41e0cafa29fcd390fd88ee72544da44c17fcb3599000000#256,
      (0x4ced47f7#32, 0x3fc368d9#32), by simpa [oneHotDifference] using cell_18_25⟩
  · exact ⟨0x00000000ea2bfffe7bcd3e120969fcb9d253f3512efd0fef93eef3d7ab3e2200#256,
      (0x8d71009a#32, 0x3c003b5f#32), by simpa [oneHotDifference] using cell_18_26⟩
  · exact ⟨0x00000000976b80002fb2d658a6ca43bef7975f6b6583ced837678ef219000000#256,
      (0x74d54d83#32, 0x6cf5134f#32), by simpa [oneHotDifference] using cell_18_27⟩
  · exact ⟨0x000000004923300087f4236943b07da064e3b4827e6eb06d64bfe248f00b0088#256,
      (0xa742c237#32, 0xeac3c111#32), by simpa [oneHotDifference] using cell_18_28⟩
  · exact ⟨0x000000003a63c000b1ec55c90ced11a368491c470edf7c32c1a69c7170001003#256,
      (0xe39032e2#32, 0xf1681d24#32), by simpa [oneHotDifference] using cell_18_29⟩
  · exact ⟨0x00000000d93d00001a05394e43ab470f9fce6c9547fd94758176cbf230003000#256,
      (0x72c1635e#32, 0xf5285f23#32), by simpa [oneHotDifference] using cell_18_30⟩
  · exact ⟨0x00000000455b0000e421848c94e970ed74f0d4854f351085e029cac8a2efbb8d#256,
      (0x894513c1#32, 0xa6db8ce5#32), by simpa [oneHotDifference] using cell_18_31⟩

end Magma.DiffanNineRoundPositiveRows
