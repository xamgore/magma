module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row15Group00
public import Magma.Diffan.NineRoundPositiveRows.Row15Group01
public import Magma.Diffan.NineRoundPositiveRows.Row15Group02
public import Magma.Diffan.NineRoundPositiveRows.Row15Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 15. -/
theorem row15 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (15 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000085c29ffffed80fbd91b4358406f41f6a41577ffed75d10a376f1cf43#256,
      (0xd2af7adf#32, 0x8a5d7ca5#32), by simpa [oneHotDifference] using cell_15_00⟩
  · exact ⟨0x00000000fccc4fff35bfdefa3dff30165acda8006a409f1c2e06f50b6cd978b7#256,
      (0x9123f615#32, 0x27920f87#32), by simpa [oneHotDifference] using cell_15_01⟩
  · exact ⟨0x000000006c6359f9e6676f4d6d3845b67c11a1222913e1aae43bf63acfaf39f9#256,
      (0x6d4b6d70#32, 0x4e1c5f99#32), by simpa [oneHotDifference] using cell_15_02⟩
  · exact ⟨0x00000000d3aa1fffa2deca5b132cd88375f6800e21ee5e2854482bdeb0a482c9#256,
      (0x020d9bfd#32, 0x026797e8#32), by simpa [oneHotDifference] using cell_15_03⟩
  · exact ⟨0x00000000eb846fff01d58987a5950ab020b1ac11773b2097a84874b11520cb70#256,
      (0x2cdabc1b#32, 0x93b73625#32), by simpa [oneHotDifference] using cell_15_04⟩
  · exact ⟨0x00000000ccd08000f564538f76519048a5524f09c6f34b560140cab3270110e0#256,
      (0x3d647412#32, 0xad010dbd#32), by simpa [oneHotDifference] using cell_15_05⟩
  · exact ⟨0x0000000028d1efff21880064afa4f3df9e5fb3f9375f105e2b274badbbf26ac7#256,
      (0x90716f84#32, 0x8df870f0#32), by simpa [oneHotDifference] using cell_15_06⟩
  · exact ⟨0x00000000e85863f9367753372162285e33bc2fa8044cebd80e4dc5f20d77b2d0#256,
      (0x418a5999#32, 0xf0ae7251#32), by simpa [oneHotDifference] using cell_15_07⟩
  · exact ⟨0x00000000d2cd0fff69cb8d704f8e24ef50417d413d568e472df324865c7f86f8#256,
      (0x3d0f451d#32, 0x76889a52#32), by simpa [oneHotDifference] using cell_15_08⟩
  · exact ⟨0x00000000fd36cfffe16097f78edb711b464117f6ed5261d7c77d16f897c475ff#256,
      (0xa38f577a#32, 0xdffc5378#32), by simpa [oneHotDifference] using cell_15_09⟩
  · exact ⟨0x00000000d6d79fc49e368dd2c5bcf32847cdaf3fc04bfa2cf56780774e63a308#256,
      (0x44a91978#32, 0x2b91ff27#32), by simpa [oneHotDifference] using cell_15_10⟩
  · exact ⟨0x000000005e2714dc58f4239355cf046863d3e6ecb6df78a6f0be62018135de00#256,
      (0xa69ee90f#32, 0x6544d37c#32), by simpa [oneHotDifference] using cell_15_11⟩
  · exact ⟨0x0000000034cfd93edd31e9c86ae0c77f90b91ff8617ab2808c2d04f6cacb2de0#256,
      (0x9ce0f635#32, 0x0179a6ea#32), by simpa [oneHotDifference] using cell_15_12⟩
  · exact ⟨0x000000005e3e33d4bdae63dd04dbfa37b348ff7d17aa16caf2fdf34e08f16460#256,
      (0x898ea335#32, 0x98879df8#32), by simpa [oneHotDifference] using cell_15_13⟩
  · exact ⟨0x00000000050ecfff8717edbadebb061ea4b07adc8209dcbb3402bd0d985e137c#256,
      (0x7ff67b36#32, 0x060baff0#32), by simpa [oneHotDifference] using cell_15_14⟩
  · exact ⟨0x0000000042138f86adece80a78de8eaf6ed5dfb487aa26510bcdb53dd9cf6860#256,
      (0x00b9e212#32, 0x77b52ec2#32), by simpa [oneHotDifference] using cell_15_15⟩
  · exact ⟨0x00000000f5a56fffe1a4250613d7f05fe77b7d60efa08cd3d61718b7fb3aff80#256,
      (0x0f134966#32, 0x3b36ad25#32), by simpa [oneHotDifference] using cell_15_16⟩
  · exact ⟨0x0000000095c01fff7d2e1abff906e1d9c71c0b710f4b5f77e768a623475f000f#256,
      (0xd1ccffcd#32, 0xcbd12e03#32), by simpa [oneHotDifference] using cell_15_17⟩
  · exact ⟨0x0000000017c97fff7b9b50d9e26599bac860a147d4a2e905882a93a2f80b838f#256,
      (0x6d91d7a2#32, 0x65760691#32), by simpa [oneHotDifference] using cell_15_18⟩
  · exact ⟨0x00000000c6c48ffffea86599ecc6dcfea2577d4e82b13935d023c56223f7dff8#256,
      (0x6aed4c76#32, 0x2af686d4#32), by simpa [oneHotDifference] using cell_15_19⟩
  · exact ⟨0x000000000dfc23ff5a4d4d0eebdf8c316e84eb4b651f6f4fba4053dbbc36b15e#256,
      (0xa9c380fc#32, 0x43e983ea#32), by simpa [oneHotDifference] using cell_15_20⟩
  · exact ⟨0x000000003bed3fc2e9949a044315f5941e6c3dbc8b1e96723f1af3b20c6c9280#256,
      (0xd4e4be62#32, 0xbe20b8de#32), by simpa [oneHotDifference] using cell_15_21⟩
  · exact ⟨0x00000000bb7d3dfb4c95fbb0e7416e73dacb81a66b452c19d277ded3f3d0ccf0#256,
      (0x88a3ac97#32, 0x02a51b2a#32), by simpa [oneHotDifference] using cell_15_22⟩
  · exact ⟨0x00000000f3724fff7fd2109d871e98dbc92bcc59aa9cee07a7b3eb054179f80f#256,
      (0x0531bf2d#32, 0x9610ca46#32), by simpa [oneHotDifference] using cell_15_23⟩
  · exact ⟨0x00000000022b706a889d120918fc108e936948571382249746c5dd26493274f8#256,
      (0x70936aac#32, 0x8fbd139b#32), by simpa [oneHotDifference] using cell_15_24⟩
  · exact ⟨0x00000000f7995fff8d0174e2b009514548c127d76b04aa6b63eb727a330d018c#256,
      (0xa55ca79b#32, 0x2feaaa6f#32), by simpa [oneHotDifference] using cell_15_25⟩
  · exact ⟨0x000000008c5f2b3f8b3441869446e4283818c6c9f89ddd24f42bdc90913a407d#256,
      (0xab007b39#32, 0x18ba3b81#32), by simpa [oneHotDifference] using cell_15_26⟩
  · exact ⟨0x000000003c32dffffeb04972e74438f21b07eccf809d1e566108ed8f39203882#256,
      (0x6e39102e#32, 0xfafc941f#32), by simpa [oneHotDifference] using cell_15_27⟩
  · exact ⟨0x000000001a48b000b879962e6176c3bce08073a6c737dbb964574d4850000000#256,
      (0x106e53e8#32, 0x878ff023#32), by simpa [oneHotDifference] using cell_15_28⟩
  · exact ⟨0x00000000c81e50000ae924fc48bcb0b2a5ccbcd6ed0e9b79b7b8830fc0000500#256,
      (0xa865d942#32, 0x74cb3e40#32), by simpa [oneHotDifference] using cell_15_29⟩
  · exact ⟨0x0000000071f6d000515cc8eb7ac59b0a39caabcee120eaf0712c2d60500e2000#256,
      (0xb95ad569#32, 0x26c6d60e#32), by simpa [oneHotDifference] using cell_15_30⟩
  · exact ⟨0x0000000095ecafffbf4b77624b437734789ddd1d9b93002c3f788ccfb0c865ac#256,
      (0xfaa34fc5#32, 0x203b26ef#32), by simpa [oneHotDifference] using cell_15_31⟩

end Magma.DiffanNineRoundPositiveRows
