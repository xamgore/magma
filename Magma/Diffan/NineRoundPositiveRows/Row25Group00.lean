module
import all Init.Data.Range.Basic
public import Magma.Diffan.SixSevenRoundOuterPositive
public import Magma.Diffan.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DiffanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 25,
    output bits 0..7. -/
theorem cell_25_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000107fffffb75715da20c57006e17ad881c1e6a0767e72d4a69bcac25f#256) ⟨k.val, by omega⟩)
      (0xec95a62d#32, 0x95a08fd6#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_25_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000032e0ffff780253bce77fba9c40a9b86bd209ff1e673895609bc41e96#256) ⟨k.val, by omega⟩)
      (0x27d731e9#32, 0x553c8d6c#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_25_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d1f3b50c04853d6993e40664b11382890e7be4eb16bb1030320fef1e#256) ⟨k.val, by omega⟩)
      (0x37ed1a86#32, 0x81a53836#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_25_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e24c4fff6085f4863a6f011ce420651993a30c8d949c89ea30b0e063#256) ⟨k.val, by omega⟩)
      (0x1371129c#32, 0x8edadc6b#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_25_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007777c597d9577f83875be6f2244caf8436a82d06e34d4e038483f088#256) ⟨k.val, by omega⟩)
      (0x23686149#32, 0xf3f77480#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_25_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009510f39c0a99e29563c107a82350827b4f6dfdb15e9944d6e204c952#256) ⟨k.val, by omega⟩)
      (0x13c1b983#32, 0xc7b9919c#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_25_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009e5881e2060e1747a3c398f32c1a336b96529c7f2df5d7c33e041c90#256) ⟨k.val, by omega⟩)
      (0xa81b4576#32, 0x4da2bfeb#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_25_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001d000000f79d8bd19989b5c2e0ee01746ffa05154886f88ce8cd0c90#256) ⟨k.val, by omega⟩)
      (0x7c321184#32, 0x2bd2de3d#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
