module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row01Group00
public import Magma.Differential.NinePlus.PositiveRows.Row01Group01
public import Magma.Differential.NinePlus.PositiveRows.Row01Group02
public import Magma.Differential.NinePlus.PositiveRows.Row01Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 1. -/
theorem row01 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (1 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000c34f495affea39619445bd42b2c60cfcf48f66a70b2bc1ffe4810405#256,
      (0x6aed8721#32, 0x7b2c1052#32), by simpa [oneHotDifference] using cell_01_00⟩
  · exact ⟨0x00000000ff55d312060dfc8b9351937d94f5db0b9dd17215f6c10701aa1992bf#256,
      (0x3086a4d5#32, 0x4fc9a24f#32), by simpa [oneHotDifference] using cell_01_01⟩
  · exact ⟨0x000000000704ebb502034ecd25d7888bd125af01437a88a7b134962163f493bb#256,
      (0x5ed12ee1#32, 0x53cd02ab#32), by simpa [oneHotDifference] using cell_01_02⟩
  · exact ⟨0x00000000717feebbb2e902e0bf5da387eb9f57ca258908d7f22e0cc28cbeb0d5#256,
      (0xa721fce9#32, 0xe37c070f#32), by simpa [oneHotDifference] using cell_01_03⟩
  · exact ⟨0x00000000157442368381ccf6a990b562b7f807ee29bb8728beb68a5a8be14590#256,
      (0xc48f5618#32, 0x1d310ffa#32), by simpa [oneHotDifference] using cell_01_04⟩
  · exact ⟨0x000000008a53a69f17ef6b204e1d1399cff9e76e4377b9c4612fffa7f15b055f#256,
      (0xe03aebe3#32, 0x5b9934d2#32), by simpa [oneHotDifference] using cell_01_05⟩
  · exact ⟨0x00000000ba78ec8bc9bb5b25b430ba65d264290fee60df420cfeebaa4236c938#256,
      (0xc34ac785#32, 0x2d89a6a0#32), by simpa [oneHotDifference] using cell_01_06⟩
  · exact ⟨0x00000000454b13a94af297c36901d0507bd3fd666389378f7c53aa1f00a63680#256,
      (0x8278d3e7#32, 0x94bc3d1b#32), by simpa [oneHotDifference] using cell_01_07⟩
  · exact ⟨0x00000000fd2a92fa1fa51946690d5667d65f121e64bc4c04ae1d6610a809290b#256,
      (0xd1aee81f#32, 0xdef3d67d#32), by simpa [oneHotDifference] using cell_01_08⟩
  · exact ⟨0x000000006f5da31ae47d15044b202f2b2f4919f2a42cdc15a52734328f2b2f0f#256,
      (0xd5b3a59d#32, 0xf854543e#32), by simpa [oneHotDifference] using cell_01_09⟩
  · exact ⟨0x000000002026ef928648519bbf2f1bc8e39390de3d801bb1f1c19fe936cb3aff#256,
      (0x48e393c6#32, 0x135c2d6c#32), by simpa [oneHotDifference] using cell_01_10⟩
  · exact ⟨0x0000000061d3e10f8e08a7611d1feba5b1b72918919a9d4b1b6196dcc14af79a#256,
      (0xe99a06a2#32, 0x4df7ce7d#32), by simpa [oneHotDifference] using cell_01_11⟩
  · exact ⟨0x00000000e5bc710185382eb5787b99db99c0bda8f2468fbd9d6b6c0bce416d00#256,
      (0xb13f3a02#32, 0xc8827542#32), by simpa [oneHotDifference] using cell_01_12⟩
  · exact ⟨0x00000000515fd1a198e9e3f0fde9f186f42273ebc881343946181756aff31520#256,
      (0x44b961df#32, 0x9b025127#32), by simpa [oneHotDifference] using cell_01_13⟩
  · exact ⟨0x00000000a55dbe2e17e99533b2cc3073629e7604499e49fcd7b5b6f41c701fff#256,
      (0xa31ba394#32, 0x80712030#32), by simpa [oneHotDifference] using cell_01_14⟩
  · exact ⟨0x00000000d0af5041087650004f4322ff643b726462cb6619eeec41701b8814d4#256,
      (0x7e203d43#32, 0xabf97888#32), by simpa [oneHotDifference] using cell_01_15⟩
  · exact ⟨0x0000000035cbc2df270bf5881ff99c9f293bbd878aefb5b715429433ba1cffff#256,
      (0xbc113a4b#32, 0x2cd40c5c#32), by simpa [oneHotDifference] using cell_01_16⟩
  · exact ⟨0x00000000903efe1f226cba0dd1c9d2fecce3b9deec6ba005fd0a98b7cae69f86#256,
      (0x2b903777#32, 0x32257622#32), by simpa [oneHotDifference] using cell_01_17⟩
  · exact ⟨0x00000000a0e7d569c489ecee35df45380baabc9f306fc346e5baafb37656bfc0#256,
      (0xb38c0f6c#32, 0xe89da811#32), by simpa [oneHotDifference] using cell_01_18⟩
  · exact ⟨0x00000000c16e6a73c8075fa60173d43c7e298c898eec16080cc916de9d89af0c#256,
      (0x91089115#32, 0xce58412c#32), by simpa [oneHotDifference] using cell_01_19⟩
  · exact ⟨0x00000000855a39ff69d10202305155a37553028c230a7f6b2042067755a00000#256,
      (0x5ccbe404#32, 0x8b13a771#32), by simpa [oneHotDifference] using cell_01_20⟩
  · exact ⟨0x00000000de57bca6737c10cb1ed7ee423d82fae18681db1c73a0bce183f00000#256,
      (0xc0de1395#32, 0x051f4c74#32), by simpa [oneHotDifference] using cell_01_21⟩
  · exact ⟨0x000000008336ef9fbba0533dbab9aaafc69228ae1bbbeaf45ee916b4e38fffff#256,
      (0x3ef0e287#32, 0x57ea7938#32), by simpa [oneHotDifference] using cell_01_22⟩
  · exact ⟨0x000000009c19381dd935137d319b4058da9153f10f345a312a4d447c49bfffc1#256,
      (0xa70bf8ed#32, 0xf8d16312#32), by simpa [oneHotDifference] using cell_01_23⟩
  · exact ⟨0x00000000c0058fd65728a4e35f3894391c6f932db7e3a9ec535ef3bacb0a5500#256,
      (0x01f44ae8#32, 0x5097095b#32), by simpa [oneHotDifference] using cell_01_24⟩
  · exact ⟨0x000000008b8097be77ebcf0a0fb45caa98a17898280f43cbf8d362090d810620#256,
      (0x1af6a6a9#32, 0x3cd2b937#32), by simpa [oneHotDifference] using cell_01_25⟩
  · exact ⟨0x00000000baebb96b29c63e9c1dd05f061d93293fd1576b81ac1254dbd11491f8#256,
      (0x5e5f8ac4#32, 0x6d0529b7#32), by simpa [oneHotDifference] using cell_01_26⟩
  · exact ⟨0x00000000b4466c6ee0ba809c0361b4e0bceaae12f75d36fe49d2487115fdc900#256,
      (0x3f2e07e1#32, 0x34b8041d#32), by simpa [oneHotDifference] using cell_01_27⟩
  · exact ⟨0x0000000002be53c02d9fc5c18f90ced65d0e05c2ae89035099e2fce528d701dc#256,
      (0x94a1ffaf#32, 0xd2ae3933#32), by simpa [oneHotDifference] using cell_01_28⟩
  · exact ⟨0x00000000465da8aaee88a1c3c996dd59cd2c57a2b3cf603fe115c50070a25400#256,
      (0x5a89e4a7#32, 0x11c35db2#32), by simpa [oneHotDifference] using cell_01_29⟩
  · exact ⟨0x000000002b667222d6281df5a534923c423db5f62af49c477b3a4a73dc2bd309#256,
      (0x1117b2a5#32, 0x28f71ccd#32), by simpa [oneHotDifference] using cell_01_30⟩
  · exact ⟨0x000000006ac4b0513a3a380bc0eb22f620c798d4db003be513f629dfef1d4034#256,
      (0xb0091d86#32, 0x8398aea4#32), by simpa [oneHotDifference] using cell_01_31⟩

end Magma.DiffanNineRoundPositiveRows
