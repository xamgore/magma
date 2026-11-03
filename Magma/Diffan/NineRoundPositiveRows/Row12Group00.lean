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

/-- Kernel-checkable real RFC Magma trajectories: input bit 12,
    output bits 0..7. -/
theorem cell_12_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000042e887ffd22a2f8aa27fa57f30705f1c69b8e4f1a602ec3a0d0c1b77#256) ⟨k.val, by omega⟩)
      (0x5be9a3bb#32, 0x4c2445d6#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_12_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005da5877ffdf8943f157c93646322e92af91604640e3ceb92fc477a4b#256) ⟨k.val, by omega⟩)
      (0x9c160d32#32, 0x2b340d18#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_12_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e8901500a68705e8403d6f793c6cfd142b8bce85c32ca2e178478b1c#256) ⟨k.val, by omega⟩)
      (0x558010c6#32, 0xffd2b7fa#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_12_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fe23d3e050fa5c9fbcd68fcbbb374d928bf7310c636db0ff3f1fe8ba#256) ⟨k.val, by omega⟩)
      (0xe695e927#32, 0xefd3dd36#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_12_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009e320fff1ddbf46616a3b77090b46c7b00c3f6b40d96252c41bda337#256) ⟨k.val, by omega⟩)
      (0x14bf0402#32, 0xe99fa868#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_12_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f0594fff72a9d073bdaf4de9cb484cb023c275aaae234d030be896e0#256) ⟨k.val, by omega⟩)
      (0xd554ee32#32, 0x5019b8a6#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_12_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a7288880106674abe20da80b65b2ef57f808675d254c6772e5dd5350#256) ⟨k.val, by omega⟩)
      (0x22c9cc23#32, 0x3185a1d1#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_12_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002c42e77af1844f04ee479afd0199ca195f0226dfe03ecd81d3aeffe0#256) ⟨k.val, by omega⟩)
      (0xf9cbd21b#32, 0xa917d8d7#32)
      (0x00001000#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
