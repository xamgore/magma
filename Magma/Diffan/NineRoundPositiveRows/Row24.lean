module
import all Init.Data.Range.Basic
public import Magma.Diffan.NineRoundPositiveRows.Row24Group00
public import Magma.Diffan.NineRoundPositiveRows.Row24Group01
public import Magma.Diffan.NineRoundPositiveRows.Row24Group02
public import Magma.Diffan.NineRoundPositiveRows.Row24Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 24. -/
theorem row24 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (24 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x00000000e688000045148723eeb65820fc63fbb98813e2d3b664eb941632fba3#256,
      (0x48e3b188#32, 0x3b189ab1#32), by simpa [oneHotDifference] using cell_24_00⟩
  · exact ⟨0x00000000ccf45fff04206e3860e039b2c1fc5f406c535aa5bea65c5d80211167#256,
      (0x90a5550e#32, 0xa3068069#32), by simpa [oneHotDifference] using cell_24_01⟩
  · exact ⟨0x0000000002c0000092f4e725a96f3decad214f770a8fd661e131c1b4e10a505d#256,
      (0x263f0728#32, 0xe6215578#32), by simpa [oneHotDifference] using cell_24_02⟩
  · exact ⟨0x000000000b6bff41e9e06a1f6c901b4180474fe03f48b78961535750c92e830a#256,
      (0xad43981e#32, 0x09f01a18#32), by simpa [oneHotDifference] using cell_24_03⟩
  · exact ⟨0x000000003b4b0c67b2058e799de780d6e04a2ccd611b932028764a52624860e2#256,
      (0x97505498#32, 0xb62d8c82#32), by simpa [oneHotDifference] using cell_24_04⟩
  · exact ⟨0x00000000770000002935cfefe2fa900c34ebde6c979e78c0382aec99db423b90#256,
      (0x43d69556#32, 0xeacfb7ef#32), by simpa [oneHotDifference] using cell_24_05⟩
  · exact ⟨0x000000001ade8bfcbf3b82651e5980080b62ea4ee0db6f93b7b39928f06bd070#256,
      (0xabdfed62#32, 0x7b7c6f4d#32), by simpa [oneHotDifference] using cell_24_06⟩
  · exact ⟨0x000000001effffff23e51558485023ce019f5feaf83b189c562502ffdc9bab6f#256,
      (0x995d1630#32, 0x7be133b0#32), by simpa [oneHotDifference] using cell_24_07⟩
  · exact ⟨0x000000004cf721e37e6b04a610f8bac6f0341755ff5ff825563734c0008d6efb#256,
      (0x973e7cce#32, 0x7c7fa4f5#32), by simpa [oneHotDifference] using cell_24_08⟩
  · exact ⟨0x0000000050ffffffac6a91fba6fff40dbcea26c685f8564714284fff4a4d55ff#256,
      (0xdfd87899#32, 0x9f1436e2#32), by simpa [oneHotDifference] using cell_24_09⟩
  · exact ⟨0x000000005edb9113198402ea84849593b0825fb08bd852451956b17b015a09c2#256,
      (0x8b074097#32, 0xd81c7b67#32), by simpa [oneHotDifference] using cell_24_10⟩
  · exact ⟨0x00000000f1000000f14b8b899b9e8cbbea3ccba2ca3c7c0002e71083ceaafb00#256,
      (0xc2308793#32, 0x7365ed92#32), by simpa [oneHotDifference] using cell_24_11⟩
  · exact ⟨0x0000000046ff80ff130443a1257dbf7ef743b07f2673fe9a6d8f05bea8ec17ff#256,
      (0x134ff99f#32, 0x443185a9#32), by simpa [oneHotDifference] using cell_24_12⟩
  · exact ⟨0x000000003561fffea9008c98c019027f205e81444508a5a2e63d852f3eb31540#256,
      (0xd8b04c36#32, 0x64a4155d#32), by simpa [oneHotDifference] using cell_24_13⟩
  · exact ⟨0x000000001ac8000030064c0c930fbf928f7fb66dbb37d00c0b4940e5777b3801#256,
      (0x123a8d00#32, 0x58960fff#32), by simpa [oneHotDifference] using cell_24_14⟩
  · exact ⟨0x0000000039ffffff9f2abd6da3b26f44d001ea62aff9422ae1c04c87b48b86ff#256,
      (0x3efc2b6d#32, 0xb959ffdb#32), by simpa [oneHotDifference] using cell_24_15⟩
  · exact ⟨0x000000002cc3ffff3a0f6b0e649c323282cced6b4c60dae8afe22faf3280d860#256,
      (0x1bc387ef#32, 0x3b9a2870#32), by simpa [oneHotDifference] using cell_24_16⟩
  · exact ⟨0x00000000170800007a4d06d02ac702ad0136025a7a38980c3d70124553e30000#256,
      (0x0a1b62d9#32, 0x234d53ad#32), by simpa [oneHotDifference] using cell_24_17⟩
  · exact ⟨0x00000000a5008000422417917c6f34161105200c4ba55a8ad01b3002ea8a0000#256,
      (0xda13e985#32, 0xfb032375#32), by simpa [oneHotDifference] using cell_24_18⟩
  · exact ⟨0x00000000f7243fff6aac3a89458d3f6443d58887d4e75db9084b67c2471ad2f0#256,
      (0xe8b03fc3#32, 0x54ad9cfb#32), by simpa [oneHotDifference] using cell_24_19⟩
  · exact ⟨0x00000000650800007dae438b20f8ee7f831014c5f70db0615dc6de12023000e0#256,
      (0x32865292#32, 0x74e0916c#32), by simpa [oneHotDifference] using cell_24_20⟩
  · exact ⟨0x00000000bac00000811d2c1296188262420b43f2785c6f8268e11fddb8300000#256,
      (0x33930248#32, 0xf6c6653d#32), by simpa [oneHotDifference] using cell_24_21⟩
  · exact ⟨0x00000000510800002d16e8e43237d55d64e5aa079342f0fed805d90e79f5f204#256,
      (0x71b02135#32, 0x3b02d9f0#32), by simpa [oneHotDifference] using cell_24_22⟩
  · exact ⟨0x0000000058808000f530641a8e4cab6e647d265767c397f0a44c4598ff400000#256,
      (0x8120b2ac#32, 0x63ff4925#32), by simpa [oneHotDifference] using cell_24_23⟩
  · exact ⟨0x00000000250800003a33f43a24f5d895ac4c370083721531d039c9e7db000000#256,
      (0xbf86d1b1#32, 0x56edf585#32), by simpa [oneHotDifference] using cell_24_24⟩
  · exact ⟨0x00000000fac800000cabe5af6fa0f41afff1dc24e151bdc5e69a80fab104e000#256,
      (0x9afbe016#32, 0x67c24b29#32), by simpa [oneHotDifference] using cell_24_25⟩
  · exact ⟨0x00000000378080004c6bb6487a480cfb6ddc645eca39a1e9e084ef10510b0000#256,
      (0x8965619b#32, 0xff06683f#32), by simpa [oneHotDifference] using cell_24_26⟩
  · exact ⟨0x00000000b680000095dac0389de8c7384239d7aaddf6379e4078fca4b4400000#256,
      (0x38e3ec80#32, 0xf35f7c47#32), by simpa [oneHotDifference] using cell_24_27⟩
  · exact ⟨0x00000000d2afff00c60aa5ea1e2d025c024f62df860e7293474b9cbd40640020#256,
      (0x373e91c5#32, 0x005e0b02#32), by simpa [oneHotDifference] using cell_24_28⟩
  · exact ⟨0x00000000388800007465847a6719afc0e14407f29757481684911afffc11780f#256,
      (0x7574bee6#32, 0x3a6b8ac8#32), by simpa [oneHotDifference] using cell_24_29⟩
  · exact ⟨0x000000008eff1000201023c32841fff15c4948c58bf10260a2b2de23d8460004#256,
      (0x29e48c7b#32, 0x1981209e#32), by simpa [oneHotDifference] using cell_24_30⟩
  · exact ⟨0x0000000075d700002705faea4b6146fdbda1f843ab495d5e292373cc320ebe22#256,
      (0xd0690add#32, 0xb3f5af81#32), by simpa [oneHotDifference] using cell_24_31⟩

end Magma.DiffanNineRoundPositiveRows
