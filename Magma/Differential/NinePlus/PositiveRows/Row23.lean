module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row23Group00
public import Magma.Differential.NinePlus.PositiveRows.Row23Group01
public import Magma.Differential.NinePlus.PositiveRows.Row23Group02
public import Magma.Differential.NinePlus.PositiveRows.Row23Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 23. -/
theorem row23 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (23 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000c35abb6a2037ebf29698ac2277f9fb8b547ed22e672a97cc9b03df7d#256,
      (0x78c09708#32, 0x1e4febc4#32), by simpa [oneHotDifference] using cell_23_00⟩
  · exact ⟨0x0000000034aabf8281bd0860e3636b91bcfe8e35293672577e8e2f2fe0ba8f2a#256,
      (0x8f62fc57#32, 0x435190fb#32), by simpa [oneHotDifference] using cell_23_01⟩
  · exact ⟨0x000000003536415e09c63351d813d1e61952a10656e24ced2d2a4a17671d436e#256,
      (0xfba29084#32, 0xde5675b1#32), by simpa [oneHotDifference] using cell_23_02⟩
  · exact ⟨0x00000000c80fc2c8b59bd16b5b0b8e88b6dc90aa940df9bed0a878109ae7fe8d#256,
      (0x02ba8934#32, 0x8b9ba33e#32), by simpa [oneHotDifference] using cell_23_03⟩
  · exact ⟨0x00000000ac8f80985b5a44e6f0bb6e15f7947b41830f20c921fadb22a44a9bea#256,
      (0x87af9303#32, 0x670a7fa8#32), by simpa [oneHotDifference] using cell_23_04⟩
  · exact ⟨0x000000006dbfffffe28409921fdcb396815d186059405fe4fb20f826525567e0#256,
      (0x53b7cdda#32, 0x365ec240#32), by simpa [oneHotDifference] using cell_23_05⟩
  · exact ⟨0x00000000a1b97635a813138f6d46a77d06fd3bf0ac8d503c68ceb6e3f4d45ca0#256,
      (0x9f40060b#32, 0xe9e4cdec#32), by simpa [oneHotDifference] using cell_23_06⟩
  · exact ⟨0x00000000f67fffff7c5aa47ce4545bff92b7361fd2c4786f93ab59dfb8a7858f#256,
      (0x36b284fc#32, 0xdb5ad9fc#32), by simpa [oneHotDifference] using cell_23_07⟩
  · exact ⟨0x00000000f77fffffaaef45f7b6978b590a2ac308d0bd467a0cfb96f82e6f8d07#256,
      (0x75967451#32, 0xf899fd14#32), by simpa [oneHotDifference] using cell_23_08⟩
  · exact ⟨0x00000000bc87ffffb5e75c37b3c9ea29ed4d87c305fe57943af37afb6721b502#256,
      (0xd548df26#32, 0xa6c34941#32), by simpa [oneHotDifference] using cell_23_09⟩
  · exact ⟨0x000000002ca1e4c66f8157201e0ae16e4fc5a73fa083ff2582e3f4ef4716ed00#256,
      (0x520fef36#32, 0xd0adcbb9#32), by simpa [oneHotDifference] using cell_23_10⟩
  · exact ⟨0x0000000063a7ffff2f03c89355e6fcd80df4519f9e136cf02554e72e67b46511#256,
      (0x55800a58#32, 0x06e59b8d#32), by simpa [oneHotDifference] using cell_23_11⟩
  · exact ⟨0x000000003240ff6f5218b74385ec40fe62bf2ef8ab540d353f5c5bda243fb700#256,
      (0x0948d13a#32, 0x1f48e4c9#32), by simpa [oneHotDifference] using cell_23_12⟩
  · exact ⟨0x00000000215ffff8ce5b6137904bf99935fed1b1960f84d35870e82938e6600f#256,
      (0x365f0160#32, 0x53d13e29#32), by simpa [oneHotDifference] using cell_23_13⟩
  · exact ⟨0x000000007d6fffff11c199c7b0f87992c4b281872f83294b490ed6c1cc9c10fe#256,
      (0x44c9640d#32, 0x1f4d823f#32), by simpa [oneHotDifference] using cell_23_14⟩
  · exact ⟨0x000000002cc47fffd4e4c2bb03e939f60028b4921c4d6cb065ee9f8289478e07#256,
      (0xef5ba0ff#32, 0x6b3c8083#32), by simpa [oneHotDifference] using cell_23_15⟩
  · exact ⟨0x00000000e6bffffff8684b0daf5c8c12d61dc631ab9e05f1e3b0de724d72f7ef#256,
      (0xa49ab792#32, 0x7cc1faf9#32), by simpa [oneHotDifference] using cell_23_16⟩
  · exact ⟨0x000000005d800000a4021d674168b14a5ee899d39080f6a065c6a81efeca0000#256,
      (0xb91f940d#32, 0x28c08281#32), by simpa [oneHotDifference] using cell_23_17⟩
  · exact ⟨0x00000000f23000003378071d67195a1bf076fd18dec1a30773f25c157f6d3000#256,
      (0x0d20b880#32, 0x0f5e3836#32), by simpa [oneHotDifference] using cell_23_18⟩
  · exact ⟨0x00000000f97000006c7643bd1f6489438ff3ec4ff381c6547010f08d5a610000#256,
      (0x5f307cab#32, 0xd8b72ca4#32), by simpa [oneHotDifference] using cell_23_19⟩
  · exact ⟨0x0000000094c7ffff32e7a525e543a62dea6d43fb854565da6ffab7af0c678ff8#256,
      (0x2cd69f3f#32, 0x1b4bb35f#32), by simpa [oneHotDifference] using cell_23_20⟩
  · exact ⟨0x000000000fb0000049d8268e9af7c5fbffaca6d0a9a9fb7edfb5087ad1580000#256,
      (0xa5e0bcc6#32, 0x5564a878#32), by simpa [oneHotDifference] using cell_23_21⟩
  · exact ⟨0x00000000ab700000087bb3ad14fcea2248a7894c1a49aea5187f8004440000d0#256,
      (0xa539e014#32, 0xf39dc402#32), by simpa [oneHotDifference] using cell_23_22⟩
  · exact ⟨0x00000000c4780000d76aa1dce81c035aefa6c2c46f7d8e23a741da7e7eb80000#256,
      (0x66096dfc#32, 0x05d5f344#32), by simpa [oneHotDifference] using cell_23_23⟩
  · exact ⟨0x00000000c4600000aa52642dbbedde34441670d2b75bcd88927abe21e9800000#256,
      (0x9b38b54e#32, 0xa894301c#32), by simpa [oneHotDifference] using cell_23_24⟩
  · exact ⟨0x0000000077b800000ddb7158f74c0934b8fd86173667c759cb460d5b85000000#256,
      (0xd14d40cf#32, 0xe6585699#32), by simpa [oneHotDifference] using cell_23_25⟩
  · exact ⟨0x0000000006b80000a6538f5b176693bbbfe239bf9113850ed54db3c7cb000080#256,
      (0x98c83ae1#32, 0x35fd3383#32), by simpa [oneHotDifference] using cell_23_26⟩
  · exact ⟨0x000000000e80000099a23d42f91bba1724d057f94ec42f3fd6713a3c27f00000#256,
      (0xc3f55ac6#32, 0x98945a64#32), by simpa [oneHotDifference] using cell_23_27⟩
  · exact ⟨0x00000000c7b00000b9ab8daa63a49c5a3e2e7f121faee3397cdac96a2c03090b#256,
      (0x1b28e8b1#32, 0x2e6e7cdd#32), by simpa [oneHotDifference] using cell_23_28⟩
  · exact ⟨0x00000000b8200000e9a526c0673a4df5c1abb2cd2a95b3834b498ce8b0cf0000#256,
      (0x8c58b2b2#32, 0xe4618b63#32), by simpa [oneHotDifference] using cell_23_29⟩
  · exact ⟨0x00000000b3b00000c954f34ebabb3c31a1a5a695ce5fa9cdf1a7f33c5847ffd0#256,
      (0x7b081da7#32, 0x49d3d1c7#32), by simpa [oneHotDifference] using cell_23_30⟩
  · exact ⟨0x00000000347c000050a523285576abd30e400ab87b5c7308ef4266f0f2d1ea78#256,
      (0x706a3057#32, 0x59856a76#32), by simpa [oneHotDifference] using cell_23_31⟩

end Magma.DiffanNineRoundPositiveRows
