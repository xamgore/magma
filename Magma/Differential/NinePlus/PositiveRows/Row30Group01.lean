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

/-- Kernel-checkable real RFC Magma trajectories: input bit 30,
    output bits 8..15. -/
theorem cell_30_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a5647fea23eaaa839ba14ae0ab7d47e7e147f3cecd03b463199548e#256) ⟨k.val, by omega⟩)
      (0x00814947#32, 0x192fa9ae#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_30_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e0003c00e1671f4198f6b5f3e9da4018079cd6e5dbf94a094282ab04#256) ⟨k.val, by omega⟩)
      (0x28ffb059#32, 0xd8b1c158#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_30_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007000000070d385421b5cdefdafd877cadf60a3b5dd3609085405db00#256) ⟨k.val, by omega⟩)
      (0x78098411#32, 0xfcf23ba2#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_30_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003c30ffff432b0c1d818212df6ef0bdd72c320d0fc5313e29090e0a00#256) ⟨k.val, by omega⟩)
      (0xf84ee900#32, 0x82f7fad0#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_30_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007000000033e7611bf17782b31ebd51e3f02954ad8972b8c7834d1008#256) ⟨k.val, by omega⟩)
      (0x61d2b0aa#32, 0x2578d0bb#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_30_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0000000ff5604797d5d06f49e08b6a958e0027d039bb443876b1000#256) ⟨k.val, by omega⟩)
      (0x1f86f8e9#32, 0x4a5a1cec#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_30_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c0000003a19ec1f2bf85d3e6910d4658aff5ea7e2275bde958ac000#256) ⟨k.val, by omega⟩)
      (0x2d2f56ae#32, 0xdf393b34#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_30_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0ffc0002f8552458da7bc23492788a1e62d0f6efcf14987c0d3f050#256) ⟨k.val, by omega⟩)
      (0x5bca9480#32, 0x0669d1d4#32)
      (0x40000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
