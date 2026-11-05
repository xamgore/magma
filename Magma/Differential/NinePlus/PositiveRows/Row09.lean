module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.PositiveRows.Row09Group00
public import Magma.Differential.NinePlus.PositiveRows.Row09Group01
public import Magma.Differential.NinePlus.PositiveRows.Row09Group02
public import Magma.Differential.NinePlus.PositiveRows.Row09Group03
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Every output bit j is reachable for input bit 9. -/
theorem row09 (j : Fin 32) :
    ∃ master : V 256, ∃ base : FeistelState,
      multiRoundDelta 9
        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)
        base (oneHotDifference (9 : Fin 32), 0#32)
        = (0#32, oneHotDifference j) := by
  fin_cases j
  · exact ⟨0x0000000079bf1a07138e5d26c0082ab16ad4cd9277b7648814b432806f78a26f#256,
      (0x267ef685#32, 0xf15e9a73#32), by simpa [oneHotDifference] using cell_09_00⟩
  · exact ⟨0x0000000034bd59ff4cd413701991744efcb17f692c072ba3ca0c2a31ccce85e6#256,
      (0xed856ac3#32, 0xd23643f7#32), by simpa [oneHotDifference] using cell_09_01⟩
  · exact ⟨0x00000000fa1fe9ec6f67ec5dabe73bc082fa00954ca35f3688675b0e4e979e8a#256,
      (0x8f304de6#32, 0x18d72fe6#32), by simpa [oneHotDifference] using cell_09_02⟩
  · exact ⟨0x00000000949b4dce5c015f81824f0308fab7b4f62eecbdee656f5d8e65c32f8b#256,
      (0x116b5768#32, 0x26e499f0#32), by simpa [oneHotDifference] using cell_09_03⟩
  · exact ⟨0x00000000bb5306ff497b603be544f680adf6c5075f82f6af217a0163cacdaf70#256,
      (0x179e20f6#32, 0x83864c67#32), by simpa [oneHotDifference] using cell_09_04⟩
  · exact ⟨0x00000000fb353dbf9cfc6420b0964bbc05eeb66b7201f6141a6c8bbca07c569f#256,
      (0xf9ea47da#32, 0x2535ab8c#32), by simpa [oneHotDifference] using cell_09_05⟩
  · exact ⟨0x00000000f8712cffcfd9a0d3b466f0cd4dfdf333c5949d8136549049e1da9d33#256,
      (0xa319630d#32, 0x08f0eef2#32), by simpa [oneHotDifference] using cell_09_06⟩
  · exact ⟨0x0000000016ca03307337781d8a5dafed2a6bb5a545be53c42c5c7ab880ad867f#256,
      (0x516b0782#32, 0xbeec90de#32), by simpa [oneHotDifference] using cell_09_07⟩
  · exact ⟨0x00000000693e90c0693f4be57a3af33681d06fdd283af4dda5b0dbc9f290ad7b#256,
      (0x9dd9caf5#32, 0x20df1181#32), by simpa [oneHotDifference] using cell_09_08⟩
  · exact ⟨0x00000000902ada005db7745746ff83c05d13b20ec0654dad7e8e88f7dce09920#256,
      (0x3cd6ad94#32, 0x8425abbf#32), by simpa [oneHotDifference] using cell_09_09⟩
  · exact ⟨0x00000000ff6472ff49ff6e31e07d741b11872faa738690849bf3c1e6be83edf8#256,
      (0xe4e9a4a9#32, 0x48e3a8a5#32), by simpa [oneHotDifference] using cell_09_10⟩
  · exact ⟨0x00000000c52205bc64982c663ba300e7c303eed1e5f9d04fcbc9c460e3b5390f#256,
      (0x0978ed7b#32, 0xeff48b53#32), by simpa [oneHotDifference] using cell_09_11⟩
  · exact ⟨0x000000004111e8ff73e2f4a232c6eeff56b10effb81ab5ac02324f4b44cc2f7f#256,
      (0xb4025a06#32, 0x9fa33717#32), by simpa [oneHotDifference] using cell_09_12⟩
  · exact ⟨0x00000000507cb9ff0a005fe6df8b262afba970a8b98ab0b7d1905bbfa3bb63ff#256,
      (0x85d93650#32, 0x7a5050a8#32), by simpa [oneHotDifference] using cell_09_13⟩
  · exact ⟨0x00000000fe6d062b4426788912ef65ae3c8428fe9f9c5650ee7a30cd24461000#256,
      (0x814b5c96#32, 0x9b9d6031#32), by simpa [oneHotDifference] using cell_09_14⟩
  · exact ⟨0x000000005dd3166192c8e61aca43be67fa96bac8d2e818c4eb4b137e6db92cfd#256,
      (0xc212c1fe#32, 0x041d9a75#32), by simpa [oneHotDifference] using cell_09_15⟩
  · exact ⟨0x00000000bec568bde83a53a1576460adde3855ff09f75638d49d89e28004c003#256,
      (0x7bf9d34f#32, 0xc581b309#32), by simpa [oneHotDifference] using cell_09_16⟩
  · exact ⟨0x0000000062c4027f73bbb923fd8038fbebd65ddff26bdd27ef0d40948cd6f80c#256,
      (0xae61ad1b#32, 0xbcd1a0a4#32), by simpa [oneHotDifference] using cell_09_17⟩
  · exact ⟨0x00000000fe3e32ff32d31ee6480899e2b96327e81b0babf638da1ecc3e6cb9a3#256,
      (0x0d00813a#32, 0xaf20e327#32), by simpa [oneHotDifference] using cell_09_18⟩
  · exact ⟨0x0000000020d13cffc9994547a426ffc36b013c1548cfee1ff7270cc673f0fff8#256,
      (0x13492828#32, 0xbf051cfa#32), by simpa [oneHotDifference] using cell_09_19⟩
  · exact ⟨0x000000008af1f22e24b0dd938cb9814b121c6623911f653b3b272332ad684960#256,
      (0x6d60533c#32, 0x385c4176#32), by simpa [oneHotDifference] using cell_09_20⟩
  · exact ⟨0x0000000005e5a1ff7a4cbc203e02fd41e7c8f0d63982da9e7c1f3ba8b951ffff#256,
      (0x6ca21ea6#32, 0x7a0acae9#32), by simpa [oneHotDifference] using cell_09_21⟩
  · exact ⟨0x0000000048469884c39b6259206032fe00aeaffaf65b6fe1629d1ba0c127dec3#256,
      (0xe8ed0842#32, 0xecb9d61a#32), by simpa [oneHotDifference] using cell_09_22⟩
  · exact ⟨0x00000000c7396eff8aae52440214797d4cb5a8b716f3780a53830c663fbfff80#256,
      (0x1acb7115#32, 0x75af59c0#32), by simpa [oneHotDifference] using cell_09_23⟩
  · exact ⟨0x00000000e13663de7fe6999a1ffe6024806cfc35f53a2a55e343e0d18ef18245#256,
      (0x31420427#32, 0x4925b9bd#32), by simpa [oneHotDifference] using cell_09_24⟩
  · exact ⟨0x00000000868148fecced044091055462ab10f8a589f1b698b45bc2115aa6b80f#256,
      (0xae2d0950#32, 0xcc7ba6bb#32), by simpa [oneHotDifference] using cell_09_25⟩
  · exact ⟨0x0000000020311d4e308eeafa26b0da3b58a574ac36ce3eef70113379fe580389#256,
      (0xd3078752#32, 0xc7c5ed20#32), by simpa [oneHotDifference] using cell_09_26⟩
  · exact ⟨0x000000001f5ea27ff81bdc835e1a31742e1fe6b6d4bd186aed5359ef0abd0003#256,
      (0x6ff0c4f1#32, 0x7b59db3d#32), by simpa [oneHotDifference] using cell_09_27⟩
  · exact ⟨0x000000008030e6ffa9b7fe46adb0fd6b71e7417d35ada757d45fcc4653ffff8f#256,
      (0x46655550#32, 0x25b842a7#32), by simpa [oneHotDifference] using cell_09_28⟩
  · exact ⟨0x000000003314f1fff0ec8483083976fdb5367278ff75db32ef70bb6b90fa3ffc#256,
      (0xf5ae296f#32, 0xcb0c5651#32), by simpa [oneHotDifference] using cell_09_29⟩
  · exact ⟨0x000000008800090043172b546516bc25464643fd8307230a7346a96d5c000080#256,
      (0x02888432#32, 0x17da4398#32), by simpa [oneHotDifference] using cell_09_30⟩
  · exact ⟨0x000000002d3ef5fe0b5b69ff0d8fa8275b37dcdefc14a857581349d1dda254b2#256,
      (0xad6db830#32, 0x0bcaf742#32), by simpa [oneHotDifference] using cell_09_31⟩

end Magma.DiffanNineRoundPositiveRows
