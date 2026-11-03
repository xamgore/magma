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
    output bits 24..31. -/
theorem cell_25_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000090000008e667d792835dc5d533f7102287f10cff641624107080000#256) ⟨k.val, by omega⟩)
      (0x24ff1064#32, 0x2f74c094#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_25_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000870000008d23c3fd2c02a664f42b3d18e13e5b221f47a3b867000000#256) ⟨k.val, by omega⟩)
      (0xd2e4583b#32, 0xa120bb46#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_25_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b6000000d0d6931882922b8c87d642c112caffde78204be4fb838000#256) ⟨k.val, by omega⟩)
      (0xa14290fb#32, 0x2e412762#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_25_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000898000001fcf9d8d67e9b7f4c8cc9a2609137b12c7165d8c8a000300#256) ⟨k.val, by omega⟩)
      (0xf7b961d7#32, 0x4ceb93cb#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_25_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007400b000596d6b56d49ab25da53e153d5d98b5a5a164b49dd8220000#256) ⟨k.val, by omega⟩)
      (0x009730f1#32, 0x29b4320e#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_25_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004e000000e2b7b59f4b3c074c303f8477fd2717278ec5149cbb7cc000#256) ⟨k.val, by omega⟩)
      (0xa5af438c#32, 0xdf83eb6e#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_25_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006d033800a7cea1772dec0f46127781de34c58d927773c3d4c00ba900#256) ⟨k.val, by omega⟩)
      (0x1451eedf#32, 0x20ae6659#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_25_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a00000095ab63446d350e0dc3e195e95a0729c217e664ef8655b379#256) ⟨k.val, by omega⟩)
      (0x66ce1b23#32, 0x3fab919e#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
