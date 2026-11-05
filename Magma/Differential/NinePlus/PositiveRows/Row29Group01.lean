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

/-- Kernel-checkable real RFC Magma trajectories: input bit 29,
    output bits 8..15. -/
theorem cell_29_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000080d000001fe8bd7bf3e68ac8c16f0bc658b84b9f14f971b3c9aa8900#256) ⟨k.val, by omega⟩)
      (0x875ab24d#32, 0x976d7820#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_29_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005af7f8bf212a2907aaa42be67291e6e156e0a5b917893b0ad4919af6#256) ⟨k.val, by omega⟩)
      (0xd804fc23#32, 0x33911d54#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_29_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000000000000b8ed8cf7fe8d953b57663532157fdd336bad78352a307a00#256) ⟨k.val, by omega⟩)
      (0x99d08035#32, 0x812ec62d#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_29_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0000000a42194e8f6f7efcb5c12dfa601783170cdafbcc01993cd00#256) ⟨k.val, by omega⟩)
      (0x8f0e8290#32, 0x9347eed5#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_29_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000de03000099266518d8473429a80ce3e2db2c2a4a038844e4e4818800#256) ⟨k.val, by omega⟩)
      (0x1ebb08d8#32, 0x7ac2a8ad#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_29_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d0000000085ed3e5767e66251901ad8963b6a7a52c782d5b80caa000#256) ⟨k.val, by omega⟩)
      (0xc164c200#32, 0x226d7277#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_29_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c38243660f3346fdaf2496257c33ca5b45c078728b03616e820c200#256) ⟨k.val, by omega⟩)
      (0xe785f0e6#32, 0xb27d8f61#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_29_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001c000000414c7c26bf0e005752848d61fac52fd077e403c3e2409800#256) ⟨k.val, by omega⟩)
      (0xc24e0d27#32, 0x2c0f1922#32)
      (0x20000000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
