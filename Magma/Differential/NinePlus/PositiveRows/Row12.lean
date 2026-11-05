module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row12Group00
public import Magma.Differential.NinePlus.PositiveRows.Row12Group01
public import Magma.Differential.NinePlus.PositiveRows.Row12Group02
public import Magma.Differential.NinePlus.PositiveRows.Row12Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 12. -/
theorem row12 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (12 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000042e887ffd22a2f8aa27fa57f30705f1c69b8e4f1a602ec3a0d0c1b77#256,
      (0x5be9a3bb#32, 0x4c2445d6#32), by simpa [oneHotDifference] using cell_12_00⟩
  · exact ⟨0x000000005da5877ffdf8943f157c93646322e92af91604640e3ceb92fc477a4b#256,
      (0x9c160d32#32, 0x2b340d18#32), by simpa [oneHotDifference] using cell_12_01⟩
  · exact ⟨0x00000000e8901500a68705e8403d6f793c6cfd142b8bce85c32ca2e178478b1c#256,
      (0x558010c6#32, 0xffd2b7fa#32), by simpa [oneHotDifference] using cell_12_02⟩
  · exact ⟨0x00000000fe23d3e050fa5c9fbcd68fcbbb374d928bf7310c636db0ff3f1fe8ba#256,
      (0xe695e927#32, 0xefd3dd36#32), by simpa [oneHotDifference] using cell_12_03⟩
  · exact ⟨0x000000009e320fff1ddbf46616a3b77090b46c7b00c3f6b40d96252c41bda337#256,
      (0x14bf0402#32, 0xe99fa868#32), by simpa [oneHotDifference] using cell_12_04⟩
  · exact ⟨0x00000000f0594fff72a9d073bdaf4de9cb484cb023c275aaae234d030be896e0#256,
      (0xd554ee32#32, 0x5019b8a6#32), by simpa [oneHotDifference] using cell_12_05⟩
  · exact ⟨0x00000000a7288880106674abe20da80b65b2ef57f808675d254c6772e5dd5350#256,
      (0x22c9cc23#32, 0x3185a1d1#32), by simpa [oneHotDifference] using cell_12_06⟩
  · exact ⟨0x000000002c42e77af1844f04ee479afd0199ca195f0226dfe03ecd81d3aeffe0#256,
      (0xf9cbd21b#32, 0xa917d8d7#32), by simpa [oneHotDifference] using cell_12_07⟩
  · exact ⟨0x00000000d1bdcd441e7131c07d1572260374701b2edae2d148f9ae2e97cbfe80#256,
      (0xac3deca8#32, 0x829695f6#32), by simpa [oneHotDifference] using cell_12_08⟩
  · exact ⟨0x000000005fe9b77e5624b8c464d3cc2a3618265196432f9a23c97c27bafcf1a8#256,
      (0xd53ba5a3#32, 0x763212c0#32), by simpa [oneHotDifference] using cell_12_09⟩
  · exact ⟨0x000000000a06cf7f8b90a3a77615c33043095e4c1d9d6c3f73624fa1c43ba4f8#256,
      (0x268b49e7#32, 0xc1a678a0#32), by simpa [oneHotDifference] using cell_12_10⟩
  · exact ⟨0x00000000c1c8aff1e11c59edfe102f2f24841a354120348a92b392aadf8e9210#256,
      (0x26febe10#32, 0x93046d38#32), by simpa [oneHotDifference] using cell_12_11⟩
  · exact ⟨0x00000000c88a2fff8268ec917b9a62f66a141373eb296cd484b07009cfd6afff#256,
      (0xe7f65a3d#32, 0xc8bd3fbd#32), by simpa [oneHotDifference] using cell_12_12⟩
  · exact ⟨0x0000000037fcaf7ff29aa71ed5ca2c0cc7d377ed598bb21ea81a69187727d8f8#256,
      (0xf4c6a6ba#32, 0x7c7b83c0#32), by simpa [oneHotDifference] using cell_12_13⟩
  · exact ⟨0x00000000bd4b0f0021ea08adf2d808419d6c4b06e4f22e2aa71dbcfb408cb57e#256,
      (0x6430242d#32, 0xa413a649#32), by simpa [oneHotDifference] using cell_12_14⟩
  · exact ⟨0x000000000650ef3f5655d67c26482b4c6ccae6df6da515ca784e5642047b5ff8#256,
      (0x11668d59#32, 0x1892ed33#32), by simpa [oneHotDifference] using cell_12_15⟩
  · exact ⟨0x0000000026c64e8005ffea6728076b0f6cfd8be550fcbb4d068985c46a72c000#256,
      (0x6b67d2f2#32, 0xb6982078#32), by simpa [oneHotDifference] using cell_12_16⟩
  · exact ⟨0x00000000b3b1d1fe6cd5178d8928911647982278514747c3022e1f1745747ed0#256,
      (0x11409bd9#32, 0x2885a9d1#32), by simpa [oneHotDifference] using cell_12_17⟩
  · exact ⟨0x00000000f1e8103f5e8072be8d7e1e1e99a7fa3d7fbb766a50ccb951e785f80f#256,
      (0xca11ea4f#32, 0xe7d15f73#32), by simpa [oneHotDifference] using cell_12_18⟩
  · exact ⟨0x00000000a17f4fffc7c81e6419eb185f2a42d730b2a7aa1980cfd72bb5e87fff#256,
      (0x308ed433#32, 0x58720978#32), by simpa [oneHotDifference] using cell_12_19⟩
  · exact ⟨0x0000000079aaf3ff19caab3fb40d2dcd3432fd9f297d7f2aa955cc65294f03ff#256,
      (0x656b44c8#32, 0x9fbdda76#32), by simpa [oneHotDifference] using cell_12_20⟩
  · exact ⟨0x000000004370efffcc9b481ad5b4ab8578c12b82f6032dd3fb3bd360b2df84c0#256,
      (0xeded031a#32, 0xd5442cac#32), by simpa [oneHotDifference] using cell_12_21⟩
  · exact ⟨0x000000002d788f7fc289d8bc4160d5c525696b3644c739dc30b0e5bc9e6ffff6#256,
      (0x47e5f6dc#32, 0x9ab8c86f#32), by simpa [oneHotDifference] using cell_12_22⟩
  · exact ⟨0x0000000023ad3000500f76c27f6742c8ebae6e4ec9421b6ee7fd211c67600000#256,
      (0x31459922#32, 0xa9d22394#32), by simpa [oneHotDifference] using cell_12_23⟩
  · exact ⟨0x00000000c9e8affe19d0df0c90826eec9d8b953fc005f7cfc9d2557d91093f92#256,
      (0xd23aac8d#32, 0xfb2fd1ca#32), by simpa [oneHotDifference] using cell_12_24⟩
  · exact ⟨0x0000000095ef2a99f3cf5c4785d1b703efb7a621055220806d151d8e74c8ffe0#256,
      (0x124d7d6e#32, 0xb6f991cb#32), by simpa [oneHotDifference] using cell_12_25⟩
  · exact ⟨0x000000000da7700062f488af3a013f7d02fe07fd0a376452364b11b736000000#256,
      (0xe76cb2cc#32, 0x90c50e15#32), by simpa [oneHotDifference] using cell_12_26⟩
  · exact ⟨0x00000000c05ddd1ce975815bfe0729de40a2d6bc5f7d7a785a041c2ff6f8c0d0#256,
      (0xf3080a1a#32, 0x577090a5#32), by simpa [oneHotDifference] using cell_12_27⟩
  · exact ⟨0x000000000a87afffaf1156828ba7f82789fb582c69dfb0a263dc66c8309035b0#256,
      (0x116bdb16#32, 0x06d4d4bf#32), by simpa [oneHotDifference] using cell_12_28⟩
  · exact ⟨0x00000000cbebcc009f0516e182006b0af6aa5bd5dc7df029051198a6c0043800#256,
      (0x46d7bbed#32, 0x2c627fbf#32), by simpa [oneHotDifference] using cell_12_29⟩
  · exact ⟨0x00000000985748008f16c11c45c7972af9df573f2d0b5ff83d69220040083000#256,
      (0xffcb35cc#32, 0x56f5acbf#32), by simpa [oneHotDifference] using cell_12_30⟩
  · exact ⟨0x00000000c06e33ff52fa5dff9ba3fb4bec003d355a3811c08cae334867aa7afe#256,
      (0x673aacb1#32, 0x6b593200#32), by simpa [oneHotDifference] using cell_12_31⟩

end Magma.DiffanNineRoundPositiveRows
