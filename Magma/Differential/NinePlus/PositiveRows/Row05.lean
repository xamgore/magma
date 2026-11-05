module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row05Group00
public import Magma.Differential.NinePlus.PositiveRows.Row05Group01
public import Magma.Differential.NinePlus.PositiveRows.Row05Group02
public import Magma.Differential.NinePlus.PositiveRows.Row05Group03
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 5. -/
theorem row05 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (5 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000a82ac0aef0220b6f34e4d903482c87613c2d117d83d90dfd045e4071#256,
      (0xa42c0563#32, 0x8b67652b#32), by simpa [oneHotDifference] using cell_05_00⟩
  · exact ⟨0x00000000221eae6f4cfabc321c857c5cf56ab41a1377b6f80c4b29db1c2e48df#256,
      (0x27ecc190#32, 0x4ed259c3#32), by simpa [oneHotDifference] using cell_05_01⟩
  · exact ⟨0x00000000558d69a0fdcbeb7ee92835929a0a8921e436cc26de8abb7b03b1c41b#256,
      (0x14c570ea#32, 0x3ba9dff0#32), by simpa [oneHotDifference] using cell_05_02⟩
  · exact ⟨0x00000000e427f6efbcbe7d1a64a48a1f9e03d945d08e09807317fb35fdeea56b#256,
      (0xae5bd79b#32, 0x3e73d8b6#32), by simpa [oneHotDifference] using cell_05_03⟩
  · exact ⟨0x00000000ec52e0f65b606202ab0eebacc0ce2daff7545f98417168c64d7d99b0#256,
      (0x1e5589e2#32, 0x375393d3#32), by simpa [oneHotDifference] using cell_05_04⟩
  · exact ⟨0x00000000eb5fe917025fe2c0182aaac0b32c408388b4b87838c9fd48a75cb830#256,
      (0x89037ba8#32, 0xa735fb0a#32), by simpa [oneHotDifference] using cell_05_05⟩
  · exact ⟨0x000000001fb58694c5c1d01a5a464e086d7b4d519fd2100832f4ad9a63428720#256,
      (0xfb785a75#32, 0xb3c9aea1#32), by simpa [oneHotDifference] using cell_05_06⟩
  · exact ⟨0x000000004cb7fe4ffc9ea325185a78ae3a878260d13e4f7ed829a1d41d2f8e7c#256,
      (0x42915916#32, 0x09824226#32), by simpa [oneHotDifference] using cell_05_07⟩
  · exact ⟨0x00000000a64ba78f4acbc42d99154ef31c9951300ae453a0091837ef000caae3#256,
      (0xbd1dde66#32, 0xdebde23c#32), by simpa [oneHotDifference] using cell_05_08⟩
  · exact ⟨0x000000002344bf1f36e7b6c9a84c60a96ac1f88a70ba1dffe4fca36b35bd358e#256,
      (0xb40dac01#32, 0xc7823eda#32), by simpa [oneHotDifference] using cell_05_09⟩
  · exact ⟨0x0000000034e22aa3f35192f23695bcbf8168396d9cccccaf31f90bc9721eed00#256,
      (0x24f2aeb0#32, 0x15aaf79e#32), by simpa [oneHotDifference] using cell_05_10⟩
  · exact ⟨0x0000000095629fa3229b80a59603dfa7e839daa004e62d0f5064bfe2ddb45850#256,
      (0x421c2376#32, 0xb6ca0e29#32), by simpa [oneHotDifference] using cell_05_11⟩
  · exact ⟨0x0000000068dac6744edd1980f2264f832faf01a74f286a6f05e523cac3c29003#256,
      (0x04243e44#32, 0x95e47f2c#32), by simpa [oneHotDifference] using cell_05_12⟩
  · exact ⟨0x000000009e2a156ae6abe5bae1441cb948908f0da5ab974c19c2caef1069e008#256,
      (0xedbd5c1a#32, 0x3ea10782#32), by simpa [oneHotDifference] using cell_05_13⟩
  · exact ⟨0x0000000018133acfca9e632356ce2584b0482ba6b91ba2d5adc4314a2bd2a006#256,
      (0x482c7e63#32, 0xba2a638b#32), by simpa [oneHotDifference] using cell_05_14⟩
  · exact ⟨0x000000002f735627d3f67375825dc96c1913ef5df10b8cec8bfaead688766fff#256,
      (0x0370b507#32, 0xc74b851d#32), by simpa [oneHotDifference] using cell_05_15⟩
  · exact ⟨0x00000000afb349dfd7d9eec8751e38e36dde72246dae03515c5111298d487c7e#256,
      (0x25f7ed2a#32, 0xb901ba06#32), by simpa [oneHotDifference] using cell_05_16⟩
  · exact ⟨0x000000004f18051f787ba29addd2664cb1c8528705f66a4071b841506e98b000#256,
      (0x76a572f7#32, 0x491f036f#32), by simpa [oneHotDifference] using cell_05_17⟩
  · exact ⟨0x0000000016b9352150ce83d0cf22a4a3eae6b2b75a0938c9cda46256dec9ce40#256,
      (0x61731632#32, 0x0cc6c079#32), by simpa [oneHotDifference] using cell_05_18⟩
  · exact ⟨0x00000000e96a1ea1bf6587ffbc441991ca8e64c47470b409900e202a903cf8cf#256,
      (0x4604d756#32, 0xd6f3f822#32), by simpa [oneHotDifference] using cell_05_19⟩
  · exact ⟨0x000000008e41512f2675d49d6f6d4f8f3ca9a7143968e3ce644f0acf0d2b86e8#256,
      (0x8ddab598#32, 0xba310c1d#32), by simpa [oneHotDifference] using cell_05_20⟩
  · exact ⟨0x000000009ffd726ff830d35f907816c6ae25ebfc7bbe408a3cc6cc897bae02fb#256,
      (0x9b8fad86#32, 0x49234951#32), by simpa [oneHotDifference] using cell_05_21⟩
  · exact ⟨0x000000003fa04e9858fd5b9e7a49a33dba008fb36edf4b4efa87a3da8063eb00#256,
      (0xb07e33fe#32, 0x54d1be3c#32), by simpa [oneHotDifference] using cell_05_22⟩
  · exact ⟨0x0000000001a06130df4b488b2a4db935dcfe395bcb763726bf21b88c85700000#256,
      (0x0cea4f99#32, 0x6158b0e7#32), by simpa [oneHotDifference] using cell_05_23⟩
  · exact ⟨0x000000009c87716fc7821fd7a248678687ebfadf7b41a093e7944fa84db8c01a#256,
      (0x0405827d#32, 0xc8d1d55f#32), by simpa [oneHotDifference] using cell_05_24⟩
  · exact ⟨0x000000006618ff5f99c4d71316621862831ced39427805c6f72815c51cfffe07#256,
      (0xda10804c#32, 0x0da688fc#32), by simpa [oneHotDifference] using cell_05_25⟩
  · exact ⟨0x00000000a7de2f0ca2de276539533ef673c9c68fe4dd2e92664c22d7224bd138#256,
      (0xeeb55f66#32, 0x94b8844f#32), by simpa [oneHotDifference] using cell_05_26⟩
  · exact ⟨0x00000000665d6bef9c043cbf858091eb8a4d34ebb5d01519b2bff493ca4ffc0a#256,
      (0xf0cb1e62#32, 0x80e29455#32), by simpa [oneHotDifference] using cell_05_27⟩
  · exact ⟨0x00000000a9cab15e18101afc521830543028ce9ae4d9825456d97bcea7a5f930#256,
      (0xd7cb98ca#32, 0xd5ed12d4#32), by simpa [oneHotDifference] using cell_05_28⟩
  · exact ⟨0x000000005377b4cfda8fb786c7235e2db6471687125310c872b974f1713383bf#256,
      (0x0a655cd7#32, 0x970f4753#32), by simpa [oneHotDifference] using cell_05_29⟩
  · exact ⟨0x00000000f5e67ecf7a11c098ee75b89c61f261aaf00886409707cc4fe7fffffc#256,
      (0x694ef6b9#32, 0x9b037698#32), by simpa [oneHotDifference] using cell_05_30⟩
  · exact ⟨0x00000000dd3b4a5c6097c9d07e9cd380a47b7aa6e4696c8804a7ee99faa35ea7#256,
      (0xba5a6466#32, 0x719131d4#32), by simpa [oneHotDifference] using cell_05_31⟩

end Magma.DifanNineRoundPositiveRows
