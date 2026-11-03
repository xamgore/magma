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

/-- Kernel-checkable real RFC Magma trajectories: input bit 1,
    output bits 0..7. -/
theorem cell_01_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c34f495affea39619445bd42b2c60cfcf48f66a70b2bc1ffe4810405#256) ⟨k.val, by omega⟩)
      (0x6aed8721#32, 0x7b2c1052#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_01_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ff55d312060dfc8b9351937d94f5db0b9dd17215f6c10701aa1992bf#256) ⟨k.val, by omega⟩)
      (0x3086a4d5#32, 0x4fc9a24f#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_01_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000704ebb502034ecd25d7888bd125af01437a88a7b134962163f493bb#256) ⟨k.val, by omega⟩)
      (0x5ed12ee1#32, 0x53cd02ab#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_01_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000717feebbb2e902e0bf5da387eb9f57ca258908d7f22e0cc28cbeb0d5#256) ⟨k.val, by omega⟩)
      (0xa721fce9#32, 0xe37c070f#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_01_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000157442368381ccf6a990b562b7f807ee29bb8728beb68a5a8be14590#256) ⟨k.val, by omega⟩)
      (0xc48f5618#32, 0x1d310ffa#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_01_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008a53a69f17ef6b204e1d1399cff9e76e4377b9c4612fffa7f15b055f#256) ⟨k.val, by omega⟩)
      (0xe03aebe3#32, 0x5b9934d2#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_01_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ba78ec8bc9bb5b25b430ba65d264290fee60df420cfeebaa4236c938#256) ⟨k.val, by omega⟩)
      (0xc34ac785#32, 0x2d89a6a0#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_01_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000454b13a94af297c36901d0507bd3fd666389378f7c53aa1f00a63680#256) ⟨k.val, by omega⟩)
      (0x8278d3e7#32, 0x94bc3d1b#32)
      (0x00000002#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
