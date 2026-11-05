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

/-- Kernel-checkable real RFC Magma trajectories: input bit 13,
    output bits 16..23. -/
theorem cell_13_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d2d5afff067c675017d2b6b4a616da5c3880b39370631e4cbafcd00a#256) ⟨k.val, by omega⟩)
      (0x389e3736#32, 0x473cce1e#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_13_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a03e0fffe042d27007b170921b0e6d737e36dae72797b98addce01c2#256) ⟨k.val, by omega⟩)
      (0xe5710cb4#32, 0x97d7be86#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_13_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004eb32380e44f446e9eb36fbc567960da4174613b243630e04ba47193#256) ⟨k.val, by omega⟩)
      (0x0dad09fb#32, 0xf21a2638#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_13_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5a7d800bb88e92d5b6fc18197b38eab82604255f9e8c3c2e0b70000#256) ⟨k.val, by omega⟩)
      (0xe5fe3e2c#32, 0xebc26b7c#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_13_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000002540dfffd4a690707cfe14095773f272a9474d369dd20751acb63ea2#256) ⟨k.val, by omega⟩)
      (0x0113b5d9#32, 0x8e478241#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_13_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000090f51e003fac0fff53a15e46f2a33900b173a12c7eb3f045eae00000#256) ⟨k.val, by omega⟩)
      (0x81c35f67#32, 0x6c8a673b#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_13_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005bf68fffc2ba6f1010e21decab025a456c97d2002c03ed4323b05b2d#256) ⟨k.val, by omega⟩)
      (0xc41fb65c#32, 0x1edfd4d9#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_13_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007c495ffe7e35f7d00250ab65e64c46ff2c73685d92c65386026bbe00#256) ⟨k.val, by omega⟩)
      (0xcc17e75a#32, 0xff11bb20#32)
      (0x00002000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
