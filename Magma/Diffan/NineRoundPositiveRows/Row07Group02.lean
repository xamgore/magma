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

/-- Kernel-checkable real RFC Magma trajectories: input bit 7,
    output bits 16..23. -/
theorem cell_07_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002882b39145e1d33100ba0092756d7b69e0a941da1b6204d835e79a00#256) ⟨k.val, by omega⟩)
      (0x3ebc34dc#32, 0x4456e32e#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_07_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000056e7695f36641d05987d7670179d95ebaeb4ecdb288d72f1223e0ffe#256) ⟨k.val, by omega⟩)
      (0x2dbdf3b4#32, 0xae1b2350#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_07_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000053fc0f8fcafb9fc1c34c2d19ca74bfe740c79c55d25284419d49fcf8#256) ⟨k.val, by omega⟩)
      (0xadffb2ba#32, 0x58dbc519#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_07_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008ff85747b873b88b8576e5ac9e80e69aec63c7d9cb2b101d7a26f28a#256) ⟨k.val, by omega⟩)
      (0xc0014d54#32, 0xe4c22ed0#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_07_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000097ec50afe3ad8472ff9c0ad3f648595290973938fb694fca9131853c#256) ⟨k.val, by omega⟩)
      (0xb6d4a023#32, 0x2430439f#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_07_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000da311386d036b5de02625b2a771719fd53aeda361ebfabc30000000#256) ⟨k.val, by omega⟩)
      (0x49befa57#32, 0x6e198ca3#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_07_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e92bd66fbdd393b61b864d3e5831fbb4e6b352b71db8479ca66fc61c#256) ⟨k.val, by omega⟩)
      (0x6663f471#32, 0xabe44ef6#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_07_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001542b0b82f139cad22408b97d8775ef62479831f20ce32bed6902e58#256) ⟨k.val, by omega⟩)
      (0x99b25a3d#32, 0xebcba993#32)
      (0x00000080#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
