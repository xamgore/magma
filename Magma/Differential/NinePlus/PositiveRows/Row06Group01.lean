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
    output bits 8..15. -/
theorem cell_06_08 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a6684d8fde6927eb531ad13707e38476706811280e4ac9fe6674213f#256) ⟨k.val, by omega⟩)
      (0x30634cee#32, 0x3e2be84e#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000100#32) := by
  decide +kernel

theorem cell_06_09 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000012fdd88eb58e46fe6c861395e284071793e8f142085476667b384d80#256) ⟨k.val, by omega⟩)
      (0x2a359e03#32, 0xf15eda4b#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000200#32) := by
  decide +kernel

theorem cell_06_10 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000007e2b69cf488906ac787088610e6306259168ea45099bbc75b2a530ff#256) ⟨k.val, by omega⟩)
      (0x5a2269a7#32, 0x9324c8de#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000400#32) := by
  decide +kernel

theorem cell_06_11 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009d46bd40227ba03ccf644e122c781041bcc16091966fb21731398b20#256) ⟨k.val, by omega⟩)
      (0x8f264ff5#32, 0xa9c0f19f#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00000800#32) := by
  decide +kernel

theorem cell_06_12 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000833233df1ffdaf34afd67d5c991c27313b60441dbd92145707073370#256) ⟨k.val, by omega⟩)
      (0x558b4c4c#32, 0x405f03dc#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00001000#32) := by
  decide +kernel

theorem cell_06_13 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004f31151cef7901473df45dc48007dc33ea4c49b5fce4d5ea65f93000#256) ⟨k.val, by omega⟩)
      (0x70b1a958#32, 0x17cf9599#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00002000#32) := by
  decide +kernel

theorem cell_06_14 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c9ec095ff8f29b9ab6d833f89de59297d8780c0f071b915c51eb5fe0#256) ⟨k.val, by omega⟩)
      (0xb72f5e90#32, 0x45e32a45#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00004000#32) := by
  decide +kernel

theorem cell_06_15 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000485f3ec4970d0a52ac7278028fb014c7e5ce76ab4459058a2e726190#256) ⟨k.val, by omega⟩)
      (0x319ac650#32, 0x22877aac#32)
      (0x00000040#32, 0#32)
      = (0#32, 0x00008000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
