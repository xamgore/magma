module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row16Group00
public import Magma.Differential.NinePlus.PositiveRows.Row16Group01
public import Magma.Differential.NinePlus.PositiveRows.Row16Group02
public import Magma.Differential.NinePlus.PositiveRows.Row16Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 16. -/
theorem row16 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (16 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000002d94ff7c985e844563d981dc9506fae72c91ae8f5b305788f0e100e5#256,
      (0xed6f89dd#32, 0xc767df19#32), by simpa [oneHotDifference] using cell_16_00⟩
  · exact ⟨0x00000000a122ffff0af04a678e46bbade1615320cca65089e54d03db407a40c2#256,
      (0xbf32c3bd#32, 0x304bc7d3#32), by simpa [oneHotDifference] using cell_16_01⟩
  · exact ⟨0x00000000109afeffe1dd6c5c24b054adb97c7244072bab4bbc6963087380371d#256,
      (0x7ab2f6ce#32, 0xecedf6f8#32), by simpa [oneHotDifference] using cell_16_02⟩
  · exact ⟨0x000000000cc32ffeccc0c43a4bb79922c26128f9d98911ec2fba13de43149939#256,
      (0x8bdc13d5#32, 0x8d2a3ce4#32), by simpa [oneHotDifference] using cell_16_03⟩
  · exact ⟨0x00000000613091f80c8f2ab8731d48016e01a5b5744c3323fb37b4090d863572#256,
      (0x6442e83c#32, 0xb03fe95b#32), by simpa [oneHotDifference] using cell_16_04⟩
  · exact ⟨0x000000008b1525fd33d4943430ae9bb2a381ffb754384601114c501fbad39cb3#256,
      (0x8df18719#32, 0x449221a7#32), by simpa [oneHotDifference] using cell_16_05⟩
  · exact ⟨0x00000000ee2f1fff2ad904eacded5484085eb579ca74ba28b120ed1937b8763f#256,
      (0x20ff7b28#32, 0x001b22f5#32), by simpa [oneHotDifference] using cell_16_06⟩
  · exact ⟨0x00000000a406ff7f39ed8f49f4e556432143043bafbc59e5222335944ac3d039#256,
      (0x14bad6be#32, 0xefaad364#32), by simpa [oneHotDifference] using cell_16_07⟩
  · exact ⟨0x00000000962a9afcbd0523829f090af40aaa0304853cfad26ba51de5fc0ad4c0#256,
      (0x98b35f82#32, 0x0b6f2c7b#32), by simpa [oneHotDifference] using cell_16_08⟩
  · exact ⟨0x000000001ab47fffccfe535a7aff09edb9d40c8b4d2f00e8e26166eb44c0de60#256,
      (0x083556d7#32, 0xd9e9a5f8#32), by simpa [oneHotDifference] using cell_16_09⟩
  · exact ⟨0x0000000031b6e9f1ac0db1a86b09d50466428cb0a91e80eab21e6818b1aa5311#256,
      (0x8b17915e#32, 0xebb6a0df#32), by simpa [oneHotDifference] using cell_16_10⟩
  · exact ⟨0x000000004312fff4a55bd7e1a1bea5472bdc38202ce0536ac791f5c9276dc90a#256,
      (0x3fc6cbc9#32, 0x70cba201#32), by simpa [oneHotDifference] using cell_16_11⟩
  · exact ⟨0x00000000e26cd14016f9b6edda1a8e208447c8198910e2458cdf43a667ed932e#256,
      (0x8c485b8c#32, 0x180ec0b5#32), by simpa [oneHotDifference] using cell_16_12⟩
  · exact ⟨0x000000008ef27ffca82dba5d805f523c95c878808447de0b5292ea670b21ceaa#256,
      (0xbaaa13db#32, 0x49b58bfc#32), by simpa [oneHotDifference] using cell_16_13⟩
  · exact ⟨0x00000000d0c2fffd51214c7dece7dc6cef6073833cd0f5a427875be93d9a3e73#256,
      (0xad71354c#32, 0x1910ad41#32), by simpa [oneHotDifference] using cell_16_14⟩
  · exact ⟨0x00000000837577c09af80063b0536c8a6be0a9c48278880ceab7945b8aa1b08e#256,
      (0x2b9714f0#32, 0x7bc6fa5d#32), by simpa [oneHotDifference] using cell_16_15⟩
  · exact ⟨0x00000000055affff709cf17678a493504a8f9a3ab6575a90ae81ccd2ebaacfff#256,
      (0x5fe1358e#32, 0x5e56a319#32), by simpa [oneHotDifference] using cell_16_16⟩
  · exact ⟨0x00000000d5b70080840951ca0533b9b10decbce3106211130ff60f45879dc000#256,
      (0x4bfdbbaf#32, 0x2efa8e1d#32), by simpa [oneHotDifference] using cell_16_17⟩
  · exact ⟨0x000000000ac2ffff75b30d81227b125738e9d54ac3b68d89805961f0bcec3f80#256,
      (0x1abdd58f#32, 0xc4556f29#32), by simpa [oneHotDifference] using cell_16_18⟩
  · exact ⟨0x00000000b082b9a8e769f90b78078333fb1e277c000cc47c91025bd0e2b7ca00#256,
      (0xb9b74613#32, 0xa5ad4d01#32), by simpa [oneHotDifference] using cell_16_19⟩
  · exact ⟨0x000000009962ffffe0bd147f059ff86453e599acd21a2f825eaa63ae7f71f80f#256,
      (0x30701343#32, 0x3e4647c3#32), by simpa [oneHotDifference] using cell_16_20⟩
  · exact ⟨0x00000000633c7fff9ef2d395fe7941ad0202cdf85c532504f4d6fb8a70f37fb8#256,
      (0x7f6b9d09#32, 0xb406c2e6#32), by simpa [oneHotDifference] using cell_16_21⟩
  · exact ⟨0x00000000b7853fff202fe4a9dfa2cced74de7bd21223e4f7c73c3bd73da7bf20#256,
      (0x7c1c4d26#32, 0xb9881cf8#32), by simpa [oneHotDifference] using cell_16_22⟩
  · exact ⟨0x000000000f54ff7ff6e10d01d7fbbde14d3ff637fc35ef430893aa124e47ffff#256,
      (0xaf662d60#32, 0xde106d42#32), by simpa [oneHotDifference] using cell_16_23⟩
  · exact ⟨0x0000000068237fff87ceacdfef63e544581c5753d390b183a49e3748e2ffcf7f#256,
      (0xcc97e032#32, 0x5c780db1#32), by simpa [oneHotDifference] using cell_16_24⟩
  · exact ⟨0x00000000dbb17fff5c690ff79b14164a8cf5d0be5d25882bdb0ff4e08e37ffff#256,
      (0x594a06a1#32, 0x6e49af50#32), by simpa [oneHotDifference] using cell_16_25⟩
  · exact ⟨0x00000000d1408000e83b477d652a828ecded5e242a0a797be5d4130fee000008#256,
      (0x5842ec9b#32, 0x79a8455d#32), by simpa [oneHotDifference] using cell_16_26⟩
  · exact ⟨0x0000000045417fff232b798585156d382426d449477fe747c20551741835df8f#256,
      (0xe76cd89d#32, 0x7d29f669#32), by simpa [oneHotDifference] using cell_16_27⟩
  · exact ⟨0x00000000b2f4c00001954115a551d7106580fb6ec8eabb344915e617a8002008#256,
      (0x1d3a79e4#32, 0x0876f8eb#32), by simpa [oneHotDifference] using cell_16_28⟩
  · exact ⟨0x00000000541cc0c0a055ef504d2eb8eb850660720e53b9af709b432f81c023c0#256,
      (0xc79907c9#32, 0xe3ba15a6#32), by simpa [oneHotDifference] using cell_16_29⟩
  · exact ⟨0x00000000d6470000458a476ad87a94018c913addb50564f5b79c0c2e90000000#256,
      (0x45268513#32, 0x648ce1f5#32), by simpa [oneHotDifference] using cell_16_30⟩
  · exact ⟨0x00000000db3508003f47791537b6744f11347827dd2f70d8beb179b0bbabcb4c#256,
      (0xebfe3b11#32, 0xc241de1f#32), by simpa [oneHotDifference] using cell_16_31⟩

end Magma.DifanNineRoundPositiveRows
