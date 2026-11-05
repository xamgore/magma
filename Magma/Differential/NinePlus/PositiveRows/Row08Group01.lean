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

/-- Kernel-checkable real RFC Magma trajectories: input bit 8,
    output bits 8..15. -/
theorem cell_08_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003513757fb9c2a419ccd80009ec68148a26b7dab33161ece31861d0ff#256) ⟨k.val, by omega⟩)
      (0xcb8db054#32, 0xb61e9c2b#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_08_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ea784ff7e0d78fb0135e53523a1c7d4e78e2f92e4ba17157f87c79f#256) ⟨k.val, by omega⟩)
      (0xff83de63#32, 0xe125adb1#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_08_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c81b736eeeb573ed5bae199b7563e04b375d11929ca3e0c8943017a#256) ⟨k.val, by omega⟩)
      (0x6d7f6a27#32, 0x5f8c9f21#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_08_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000985650f07fbbcbfab7054018449cb28d2ff55fb0a9bbb1ff0c1c5bc0#256) ⟨k.val, by omega⟩)
      (0xfc5aab56#32, 0xea53cc0c#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_08_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000065c0ccbf53e799f6a0036f34d5fd55232895d5b879b3854316e94810#256) ⟨k.val, by omega⟩)
      (0x5daaaefb#32, 0xe3bd64cd#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_08_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0bd9aff844576f2b47bb4a6c8bdc7edbe72380b384e4a1329acb200#256) ⟨k.val, by omega⟩)
      (0x9910909f#32, 0xa74f0668#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_08_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001c93e280c76a7fcf7627174428073c8f9c676982bd7e0108fc083f00#256) ⟨k.val, by omega⟩)
      (0x43a0d0fc#32, 0xaf633d47#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_08_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008eff837f8e768f1d911958e495825e8cfbe5f1f6684fdf8235a77ff8#256) ⟨k.val, by omega⟩)
      (0x14f65268#32, 0xdd6f6f75#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
