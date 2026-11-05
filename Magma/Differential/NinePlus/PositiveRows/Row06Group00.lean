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

/-- Kernel-checkable real RFC Magma trajectories: input bit 6,
    output bits 0..7. -/
theorem cell_06_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000082bf6fc1c2499e2c53ce87556619c6df6db7d252a0b48d9f552da667#256) ⟨k.val, by omega⟩)
      (0x4c59c728#32, 0x210d2124#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_06_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000923ede3002b62b9e675b7fda1bbad25cdfc98535707590540969a6c2#256) ⟨k.val, by omega⟩)
      (0x5c49433b#32, 0x5d72c9e0#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_06_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000089d0222f46c60d5ee94517301d5f1954ebd26d8b9319842d00bdbe49#256) ⟨k.val, by omega⟩)
      (0x08a4fec2#32, 0xb2ba4901#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_06_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f9054fc0015cdac6c2eed5336d898d49fe044de65993115190d48f25#256) ⟨k.val, by omega⟩)
      (0xb067bcb0#32, 0xc67a315f#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_06_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000afe56d6c18cc62004ded6061bb4a81c2fe9737929533906684b0268#256) ⟨k.val, by omega⟩)
      (0xf92cc76e#32, 0xd9ec125a#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_06_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f20ccdbfa3d3bfdccb19a1adcec42bf43c636b096271b877325e8b58#256) ⟨k.val, by omega⟩)
      (0xcb2f2148#32, 0xb6d08013#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_06_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fcf6beb45d431f3d43ad95e11bdb59c309a0b7e6ce7e27423d5408cf#256) ⟨k.val, by omega⟩)
      (0x6f77503b#32, 0xfa459173#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_06_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c2d4cdc00808db681f1015eae7fe00fc0d4ffcfa20116d4cc6680e74#256) ⟨k.val, by omega⟩)
      (0x408304c7#32, 0x3de042e2#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
