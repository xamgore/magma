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

/-- Kernel-checkable real RFC Magma trajectories: input bit 1,
    output bits 24..31. -/
theorem cell_01_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c0058fd65728a4e35f3894391c6f932db7e3a9ec535ef3bacb0a5500#256) ⟨k.val, by omega⟩)
      (0x01f44ae8#32, 0x5097095b#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_01_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008b8097be77ebcf0a0fb45caa98a17898280f43cbf8d362090d810620#256) ⟨k.val, by omega⟩)
      (0x1af6a6a9#32, 0x3cd2b937#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_01_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000baebb96b29c63e9c1dd05f061d93293fd1576b81ac1254dbd11491f8#256) ⟨k.val, by omega⟩)
      (0x5e5f8ac4#32, 0x6d0529b7#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_01_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b4466c6ee0ba809c0361b4e0bceaae12f75d36fe49d2487115fdc900#256) ⟨k.val, by omega⟩)
      (0x3f2e07e1#32, 0x34b8041d#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_01_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000002be53c02d9fc5c18f90ced65d0e05c2ae89035099e2fce528d701dc#256) ⟨k.val, by omega⟩)
      (0x94a1ffaf#32, 0xd2ae3933#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_01_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000465da8aaee88a1c3c996dd59cd2c57a2b3cf603fe115c50070a25400#256) ⟨k.val, by omega⟩)
      (0x5a89e4a7#32, 0x11c35db2#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_01_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002b667222d6281df5a534923c423db5f62af49c477b3a4a73dc2bd309#256) ⟨k.val, by omega⟩)
      (0x1117b2a5#32, 0x28f71ccd#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_01_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006ac4b0513a3a380bc0eb22f620c798d4db003be513f629dfef1d4034#256) ⟨k.val, by omega⟩)
      (0xb0091d86#32, 0x8398aea4#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
