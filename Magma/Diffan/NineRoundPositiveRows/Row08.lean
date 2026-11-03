module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row08Group00
public import Magma.Diffan.NineRoundPositiveRows.Row08Group01
public import Magma.Diffan.NineRoundPositiveRows.Row08Group02
public import Magma.Diffan.NineRoundPositiveRows.Row08Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 8. -/
theorem row08 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (8 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000033e70eff404aa69d34aca51c2b11141b4a18d5f5bbda87e1581f4e23#256,
      (0x40885fbf#32, 0xdb838e85#32), by simpa [oneHotDifference] using cell_08_00⟩
  · exact ⟨0x000000000b511b0050ffc1bdfc4b0946200e966999bed48b69a2b807f1711db2#256,
      (0x02ae4e22#32, 0x1ffd6e85#32), by simpa [oneHotDifference] using cell_08_01⟩
  · exact ⟨0x0000000081a28eff152093f095827a9b55764dc45e5c425cafcf24590ba0280c#256,
      (0x51e2bf55#32, 0xd0406af7#32), by simpa [oneHotDifference] using cell_08_02⟩
  · exact ⟨0x0000000053ffb49f090350af36f0a63a403b58e51c7c140739140ef21a69df2a#256,
      (0xf165b901#32, 0x5d40acc8#32), by simpa [oneHotDifference] using cell_08_03⟩
  · exact ⟨0x00000000b56f02bab80910caba679a786012c89107be818596a30a162584aa4c#256,
      (0xcd8deb64#32, 0xd3dfd153#32), by simpa [oneHotDifference] using cell_08_04⟩
  · exact ⟨0x000000005a8fbf00d40dc0b6e9bfe0e769c9e789a3157846aee323b6ae8242d0#256,
      (0xa6d9710e#32, 0x7c813222#32), by simpa [oneHotDifference] using cell_08_05⟩
  · exact ⟨0x00000000018e5f3c59d2aacfdb89a44ff6f663ac69e5a03513ddf3bae19ef2b8#256,
      (0x0160daea#32, 0x5322d42e#32), by simpa [oneHotDifference] using cell_08_06⟩
  · exact ⟨0x00000000edd164ff3803a4bbae7a583b1e81080d32e42ad4b634c8feefc20570#256,
      (0xa1913b19#32, 0x0339bdf1#32), by simpa [oneHotDifference] using cell_08_07⟩
  · exact ⟨0x000000003513757fb9c2a419ccd80009ec68148a26b7dab33161ece31861d0ff#256,
      (0xcb8db054#32, 0xb61e9c2b#32), by simpa [oneHotDifference] using cell_08_08⟩
  · exact ⟨0x000000008ea784ff7e0d78fb0135e53523a1c7d4e78e2f92e4ba17157f87c79f#256,
      (0xff83de63#32, 0xe125adb1#32), by simpa [oneHotDifference] using cell_08_09⟩
  · exact ⟨0x000000009c81b736eeeb573ed5bae199b7563e04b375d11929ca3e0c8943017a#256,
      (0x6d7f6a27#32, 0x5f8c9f21#32), by simpa [oneHotDifference] using cell_08_10⟩
  · exact ⟨0x00000000985650f07fbbcbfab7054018449cb28d2ff55fb0a9bbb1ff0c1c5bc0#256,
      (0xfc5aab56#32, 0xea53cc0c#32), by simpa [oneHotDifference] using cell_08_11⟩
  · exact ⟨0x0000000065c0ccbf53e799f6a0036f34d5fd55232895d5b879b3854316e94810#256,
      (0x5daaaefb#32, 0xe3bd64cd#32), by simpa [oneHotDifference] using cell_08_12⟩
  · exact ⟨0x00000000c0bd9aff844576f2b47bb4a6c8bdc7edbe72380b384e4a1329acb200#256,
      (0x9910909f#32, 0xa74f0668#32), by simpa [oneHotDifference] using cell_08_13⟩
  · exact ⟨0x000000001c93e280c76a7fcf7627174428073c8f9c676982bd7e0108fc083f00#256,
      (0x43a0d0fc#32, 0xaf633d47#32), by simpa [oneHotDifference] using cell_08_14⟩
  · exact ⟨0x000000008eff837f8e768f1d911958e495825e8cfbe5f1f6684fdf8235a77ff8#256,
      (0x14f65268#32, 0xdd6f6f75#32), by simpa [oneHotDifference] using cell_08_15⟩
  · exact ⟨0x0000000083779b7f67b91516d23268d02aac039e8f8499e5fac8dd9acaa0fff8#256,
      (0x86979bde#32, 0x356151fe#32), by simpa [oneHotDifference] using cell_08_16⟩
  · exact ⟨0x00000000060a893f6434f65663e7e8861f171833ca292d9b84284a67f63e7fcf#256,
      (0x6cca6c9a#32, 0x86f65d9d#32), by simpa [oneHotDifference] using cell_08_17⟩
  · exact ⟨0x00000000b8eed6ceb92146167b86b0c7c1ce84489e739efdf7d1ca9c790c3810#256,
      (0xc282ea81#32, 0x1056f4b9#32), by simpa [oneHotDifference] using cell_08_18⟩
  · exact ⟨0x000000002056a2ffdb7ceb6f4432da4e85b5d3deb373f2d88956ccdb51f6ff0f#256,
      (0x981b27bb#32, 0xb3af6eae#32), by simpa [oneHotDifference] using cell_08_19⟩
  · exact ⟨0x0000000037e92cff1fd5f42b6d1b9d101bf1be2882a77a396564189d452a1fff#256,
      (0xbb225634#32, 0xe0c7a34c#32), by simpa [oneHotDifference] using cell_08_20⟩
  · exact ⟨0x0000000079ea7700258435eeaeffe6f07a60af5283115034567fe5d9a4180050#256,
      (0xe5d944b9#32, 0x6d9d4147#32), by simpa [oneHotDifference] using cell_08_21⟩
  · exact ⟨0x00000000fb51f51110d06924958afdf944bb2a6e74d0e32552e0cefaf72c23c0#256,
      (0x407daca6#32, 0x2964c6b1#32), by simpa [oneHotDifference] using cell_08_22⟩
  · exact ⟨0x00000000700814ffefc989011cccc43fa4b2f6ffe3c8a57e0d63f03633dcfffe#256,
      (0x2a233884#32, 0x10c3fb44#32), by simpa [oneHotDifference] using cell_08_23⟩
  · exact ⟨0x00000000271f35000b70943102682f44d97129572846d0a0a4b0bcece5080008#256,
      (0x7e95116e#32, 0x187f08c6#32), by simpa [oneHotDifference] using cell_08_24⟩
  · exact ⟨0x00000000a66160ff2491ee3ca61748dc9b32075a3674376e2fdb0e67d77fd007#256,
      (0x6600c10a#32, 0xd8c19d76#32), by simpa [oneHotDifference] using cell_08_25⟩
  · exact ⟨0x00000000ef96a31e83ae2311a2c6ae227b5764d166c90c9239c465243626140a#256,
      (0x5941a22a#32, 0x95c7228e#32), by simpa [oneHotDifference] using cell_08_26⟩
  · exact ⟨0x000000007ef122fe17477bb962847de08207673b811c0aefdb8f3de8d7cabf70#256,
      (0xc5cbb372#32, 0x97ff835a#32), by simpa [oneHotDifference] using cell_08_27⟩
  · exact ⟨0x000000008089e4fffcf13b495c25ba51028ff936ca9eaa748c036f78ace1e522#256,
      (0xc83192df#32, 0xfa3bd3ff#32), by simpa [oneHotDifference] using cell_08_28⟩
  · exact ⟨0x0000000070ada4ff462ea4401e3a81a12f537bc9af30a0357ba3e0e13f60ffff#256,
      (0x953ca34a#32, 0x0f0257de#32), by simpa [oneHotDifference] using cell_08_29⟩
  · exact ⟨0x00000000fa4a2099b1dd22c448d27e6c2ea9daf48b4b427db2da3d5d7a104000#256,
      (0x309efac0#32, 0xa9181001#32), by simpa [oneHotDifference] using cell_08_30⟩
  · exact ⟨0x000000006b3bc4f964bf6d632424b59b811c38eb34f67bfacbe95bc32c5ba5e3#256,
      (0xb7cc5a0e#32, 0xfdbb29e0#32), by simpa [oneHotDifference] using cell_08_31⟩

end Magma.DiffanNineRoundPositiveRows
