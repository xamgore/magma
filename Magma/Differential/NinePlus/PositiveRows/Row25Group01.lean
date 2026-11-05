module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 25,
    output bits 8..15. -/
theorem cell_25_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c540ffff71c9693f14ae371bf3e2f7f83f60d257c43f66b71f95ace0#256) ⟨k.val, by omega⟩)
      (0x1ba15c81#32, 0xb5db5ab5#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_25_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006e000000803c374180dec440f07fb47483cfdf36c9415444dcb0f180#256) ⟨k.val, by omega⟩)
      (0x74723a3f#32, 0x78666bc9#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_25_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004d25ffff8ec75ad9cf33e5cae8daebd02292080728c61d3790a8aa3f#256) ⟨k.val, by omega⟩)
      (0x122eec2f#32, 0x836bc4fb#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_25_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004effffff0a2475401180041e065bbc0c017e8208b4f82deb0de623f8#256) ⟨k.val, by omega⟩)
      (0x49de03a9#32, 0x5b52c3a7#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_25_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fb000000f8a873e3b0d8a8b8da6066bf881fbacae33210a0390e0080#256) ⟨k.val, by omega⟩)
      (0xc84c97e8#32, 0xf7871091#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_25_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000081000000a58fec22434701788c098cfdfd22f8ec769ee7e4127f1000#256) ⟨k.val, by omega⟩)
      (0x96c1b6d5#32, 0x412224c0#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_25_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000007e00000f37da81f3f9ec46072db84d6755c93bab05f72eef69d1000#256) ⟨k.val, by omega⟩)
      (0x695c6eb1#32, 0x682fa86d#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_25_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000027765ffd04d9a92543443e2409670e874cced7b6949a55973869a00d#256) ⟨k.val, by omega⟩)
      (0x4db23792#32, 0xd8ae6d2b#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
