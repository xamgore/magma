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

/-- Kernel-checkable real RFC Magma trajectories: input bit 18,
    output bits 8..15. -/
theorem cell_18_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c74500002f69d95295ac76f1f6c718fd112494059308eecc36246f00#256) ⟨k.val, by omega⟩)
      (0xf65c7cd8#32, 0xbf8c0b15#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_18_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000057b4f96d8dfd4b57ec55d60e217606925096d0a4843f5b1a3753b290#256) ⟨k.val, by omega⟩)
      (0x33406008#32, 0x3edd795d#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_18_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a1d30000df721f4b29a76aa8d4f1fb73ef904636211bf3aa72560a00#256) ⟨k.val, by omega⟩)
      (0x012fd7aa#32, 0x9e41dfe1#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_18_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f28cfd84ae0687e726c20275eae2673d1abd041f4aacab5027e4dc80#256) ⟨k.val, by omega⟩)
      (0xb68663c0#32, 0x20e34609#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_18_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000d4b8e822b641f36d2f8bb56cd47a70398ec2cb9b4da427dc597eca2#256) ⟨k.val, by omega⟩)
      (0x89b4bfc8#32, 0x3442fb39#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_18_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f7f3ffff4423cd81eb76930701661d9e73f65178ffae738bea334fff#256) ⟨k.val, by omega⟩)
      (0x6fc93c6d#32, 0x850d6eba#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_18_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fbadf3fa6115edae6e1d3c7fc8de81a280b3758bc7b3925a0d02907e#256) ⟨k.val, by omega⟩)
      (0x6b194991#32, 0x034cdd59#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_18_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000f543f625f12c350c2de3de13e467b18f84e1f1d25148d90b0405fa1#256) ⟨k.val, by omega⟩)
      (0x41558503#32, 0xeee2c547#32)
      (0x00040000#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
