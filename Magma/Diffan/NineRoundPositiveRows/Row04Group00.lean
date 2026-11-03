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

/-- Kernel-checkable real RFC Magma trajectories: input bit 4,
    output bits 0..7. -/
theorem cell_04_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000008648db05ed438dccaa18f202c2a1a5e42a723a2c53786bc75aeb26f#256) ⟨k.val, by omega⟩)
      (0x13d74965#32, 0xb456101b#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_04_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008fe1e0b700fc56ee8cdc2307608d89be021357cc7450196e4f722dae#256) ⟨k.val, by omega⟩)
      (0x4bb7207e#32, 0x2389822b#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_04_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ecbba3378e74bb00dcf8e5842460e48aa2c7a49bcb29e87d32332623#256) ⟨k.val, by omega⟩)
      (0x55923130#32, 0xe15e467a#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_04_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000092fa650f947aa936a88a03ba4731a07088d6bb4faceadfad74b238cb#256) ⟨k.val, by omega⟩)
      (0xf3dc194f#32, 0x197c303c#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_04_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d8e71ca5899a4dd8b8d32bfcecb8dcd3e868bab53848c6875e0d7470#256) ⟨k.val, by omega⟩)
      (0x548f84fb#32, 0x998e8490#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_04_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000061144cec0de19ccef6ee4fc0eea5171986afd1999597035d92e3857b#256) ⟨k.val, by omega⟩)
      (0x226777b3#32, 0xc465c249#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_04_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001a5b1f2c8ee5780987a06d08182bc9352e26923673746286f6fa2c66#256) ⟨k.val, by omega⟩)
      (0x6829673b#32, 0x9c70fdcc#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_04_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004d45e1af1f049f45b8942a48eb769460245404441baa0da8abc23db0#256) ⟨k.val, by omega⟩)
      (0x3d12fd68#32, 0xb4f38280#32)
      (0x00000010#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
