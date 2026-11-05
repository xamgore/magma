module
import all Init.Data.Range.Basic
public import Magma.Differential.SevenRounds.SixSevenRoundOuterPositive
public import Magma.Differential.FiveRounds.FiveRoundUniversalSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
@[expose] public section
namespace Magma.DifanNineRoundPositiveRows
open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundUniversalSupport

/-- Kernel-checkable real RFC Magma trajectories: input bit 27,
    output bits 16..23. -/
theorem cell_27_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b50000005ee3911a05f3f3a0a9014dfc39eebe905f654914fecac0ab#256) ⟨k.val, by omega⟩)
      (0x8307d954#32, 0x2228fc69#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_27_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a0fefcfe05c5b90368005b44f866e7c18c09c79add0178d84a5cf96d#256) ⟨k.val, by omega⟩)
      (0x26f95986#32, 0xe1a4278d#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_27_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e5000000e1ae31b5414828087a2b03cf96e6f114c6e229794ed20000#256) ⟨k.val, by omega⟩)
      (0x0e2192b9#32, 0xae6387ff#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_27_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a0000007018b8955b1834dd25b557170c427e1dd9308a6e424a5000#256) ⟨k.val, by omega⟩)
      (0xa0414d7e#32, 0x540ac0d5#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_27_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e8000000792ca3ea886ecba8fa0731bbd0b9730966c725d0d5cf80a0#256) ⟨k.val, by omega⟩)
      (0x801fbbc0#32, 0x97809abf#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_27_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001d0001000c1018c92fb8396b230c1d254b061475c44ff28bf3de0000#256) ⟨k.val, by omega⟩)
      (0x1b92011a#32, 0x8f0e803e#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_27_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008a0000004930e2c8268510e4dfcf1d2c0ea1b018acce855b5ae00000#256) ⟨k.val, by omega⟩)
      (0x8442b075#32, 0x83b202c4#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_27_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000093000000a6b90e6e7bcfb067b78e942a3869efa3ef6e0ce3f5c1dc00#256) ⟨k.val, by omega⟩)
      (0x2fdff2e8#32, 0xe52fbd60#32)
      (0x08000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
