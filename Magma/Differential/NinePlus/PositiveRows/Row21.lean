module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row21Group00
public import Magma.Differential.NinePlus.PositiveRows.Row21Group01
public import Magma.Differential.NinePlus.PositiveRows.Row21Group02
public import Magma.Differential.NinePlus.PositiveRows.Row21Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 21. -/
theorem row21 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (21 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x000000003fc00000dd7ea0d145976500e6402034d61fdf7ad0ddc1fb01627109#256,
      (0x7b84445f#32, 0x808531bf#32), by simpa [oneHotDifference] using cell_21_00⟩
  · exact ⟨0x00000000c0ca3df08c4d03b8b11c97e00b95dea065255addc8bb46b870d9bf15#256,
      (0xd42837fe#32, 0x71d5743c#32), by simpa [oneHotDifference] using cell_21_01⟩
  · exact ⟨0x00000000d9dfffff6033c5ad75844a9a5c76f750acb0dc87140a71aba56c2035#256,
      (0xc51a6d16#32, 0x7fae7f72#32), by simpa [oneHotDifference] using cell_21_02⟩
  · exact ⟨0x00000000361ffd794abb04cd06d17e33fdff5e3440a4004cec87e12ae14c95e9#256,
      (0x9bdb950c#32, 0x965352b6#32), by simpa [oneHotDifference] using cell_21_03⟩
  · exact ⟨0x0000000097efffff36421a855065fc74ab6817172aaddc34c96a5efec4f17108#256,
      (0xcd401dd7#32, 0x16e8accb#32), by simpa [oneHotDifference] using cell_21_04⟩
  · exact ⟨0x00000000f749b10dc2d49dbff5fc71eb9b5f82be9addeea4481c8fe3e21b57de#256,
      (0xfb4a905d#32, 0xcf64851b#32), by simpa [oneHotDifference] using cell_21_05⟩
  · exact ⟨0x00000000e71fffff1cd4d91b2876638b49614becea5fd44309dffbd36049fc9d#256,
      (0xd7fe13a0#32, 0xd855d473#32), by simpa [oneHotDifference] using cell_21_06⟩
  · exact ⟨0x0000000073b00000f8218c6004b52fe42bec143047c821c03a14e7837fc988c0#256,
      (0x68b8f80e#32, 0xfdabe8f0#32), by simpa [oneHotDifference] using cell_21_07⟩
  · exact ⟨0x000000005a2efffeffdf4cea8cefb742421c0483c50423ddf74fad02e73d2c8c#256,
      (0x1862bf95#32, 0xc185ff80#32), by simpa [oneHotDifference] using cell_21_08⟩
  · exact ⟨0x00000000cf10ffff6e7ca7ef28f713f4c3d8999a523e53c37eb2d5895c487f0d#256,
      (0x1168c3be#32, 0x00b54411#32), by simpa [oneHotDifference] using cell_21_09⟩
  · exact ⟨0x000000008ad00000026e1990e04e886b35b1bd24f69384a7469e3d09c9f4e100#256,
      (0x256bfa0c#32, 0x97fe965b#32), by simpa [oneHotDifference] using cell_21_10⟩
  · exact ⟨0x000000000d9fffff62df55e001f047f7237df8b3f67a951ead1405db00430700#256,
      (0x7e3833e5#32, 0x0a5110fb#32), by simpa [oneHotDifference] using cell_21_11⟩
  · exact ⟨0x0000000025e3ffff0d3023eafbf94113e9fe9df7fa3361b0fb3b3afa2ee6b404#256,
      (0x78199edc#32, 0xaddf5f64#32), by simpa [oneHotDifference] using cell_21_12⟩
  · exact ⟨0x000000004952278055b5beee362b18098a788cfc5640d2e79ef9cdd3e860b41f#256,
      (0x22497d4f#32, 0xc9d8bcd1#32), by simpa [oneHotDifference] using cell_21_13⟩
  · exact ⟨0x00000000a29fffff72db0571d59e6bfba2400a77bc59e7fbd77a84048544dfcf#256,
      (0xd39f9f01#32, 0x87094da5#32), by simpa [oneHotDifference] using cell_21_14⟩
  · exact ⟨0x000000004daf80ffe8e524d05f6e0e989e7cc98f075fde99e98e1a0f9b757fe0#256,
      (0x1aafb68a#32, 0x25373d57#32), by simpa [oneHotDifference] using cell_21_15⟩
  · exact ⟨0x000000006329fcb57878c96280a6b88c9bfe608dbf34bf72fcf329d6493b180d#256,
      (0xd40af1a7#32, 0x3c19ccd0#32), by simpa [oneHotDifference] using cell_21_16⟩
  · exact ⟨0x00000000545000005cba8d3252d7c365b5420fe00d8316a2624f383157d60780#256,
      (0xbc9bab67#32, 0x5d1ed2a2#32), by simpa [oneHotDifference] using cell_21_17⟩
  · exact ⟨0x0000000042f00000daf261abe4f380e433f83606089cd34811ba4dd0c5e50080#256,
      (0x86ea4def#32, 0xe8418df5#32), by simpa [oneHotDifference] using cell_21_18⟩
  · exact ⟨0x000000005ad00000c8bae450a25562b075d54c8520ee67aa43c3a03df177c000#256,
      (0xa13b091b#32, 0xa4241b11#32), by simpa [oneHotDifference] using cell_21_19⟩
  · exact ⟨0x000000007fb0000050cacdf381387fc3c033d3d1c5148338f261140148840000#256,
      (0x727e413b#32, 0xf95f5a10#32), by simpa [oneHotDifference] using cell_21_20⟩
  · exact ⟨0x000000000e9000001f3120ec148ab63ca073cebf888f9a090b4b1b6049f00300#256,
      (0x9249c6e2#32, 0x371e51a8#32), by simpa [oneHotDifference] using cell_21_21⟩
  · exact ⟨0x000000003270000036e8edbbebc33ce5758818435b0214ac4c57db95f9420000#256,
      (0x42dae639#32, 0x10b1d5a1#32), by simpa [oneHotDifference] using cell_21_22⟩
  · exact ⟨0x00000000d2dfc000307f507300338bfe070c24f4c5a322f56fb266f068510000#256,
      (0x8275ad97#32, 0x395e2cce#32), by simpa [oneHotDifference] using cell_21_23⟩
  · exact ⟨0x00000000093000000327fabf027100aa2b8505827a794ff77eec8c3ec5200000#256,
      (0xcecc06ef#32, 0x747a9b07#32), by simpa [oneHotDifference] using cell_21_24⟩
  · exact ⟨0x000000003eb0000022908ddc390c6ef075c330deb7efcb0d896f351dc22000d0#256,
      (0xa226db65#32, 0x4d5ea35d#32), by simpa [oneHotDifference] using cell_21_25⟩
  · exact ⟨0x0000000039d000008f3265f040e7abb922b1a5137cb80619d9daa9d149000000#256,
      (0xb45b7a58#32, 0x142593cf#32), by simpa [oneHotDifference] using cell_21_26⟩
  · exact ⟨0x00000000f4700000fc47e2ce0d73c863a021f7c2b5a17e21fe045c7af7600000#256,
      (0x53b22520#32, 0xb209aaa4#32), by simpa [oneHotDifference] using cell_21_27⟩
  · exact ⟨0x0000000091200000ba9b25a17e9b826c44a46b7c1a94d0b3ab45bf1d74020000#256,
      (0x359bca80#32, 0xfd727375#32), by simpa [oneHotDifference] using cell_21_28⟩
  · exact ⟨0x00000000f52000002ef36095ea4f97bb77a488387dc3365b53d79da7bc2b0000#256,
      (0xf9c0216c#32, 0x9cbc4c84#32), by simpa [oneHotDifference] using cell_21_29⟩
  · exact ⟨0x00000000961800008b1af4869a9afe4d479816c8a2f31fa740fba6bff0082000#256,
      (0xefdd4756#32, 0xe8cf0bd0#32), by simpa [oneHotDifference] using cell_21_30⟩
  · exact ⟨0x00000000f9500000488fc785fe88793a72fa5b8dfda49cf49392b270875de5d3#256,
      (0x73a7fb7b#32, 0xc3f6aea3#32), by simpa [oneHotDifference] using cell_21_31⟩

end Magma.DifanNineRoundPositiveRows
