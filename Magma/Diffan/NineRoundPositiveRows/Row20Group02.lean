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

/-- Kernel-checkable real RFC Magma trajectories: input bit 20,
    output bits 16..23. -/
theorem cell_20_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000836e0000bf9b3aa96f9e70ade6be0bb431f892da06b5f5d888935f00#256) ⟨k.val, by omega⟩)
      (0x74b05c1a#32, 0x2c429b0c#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_20_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000061d000003d327caea7e74d266bb5f0808107e9f4524775be64890000#256) ⟨k.val, by omega⟩)
      (0xfa30e540#32, 0x08861f6a#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_20_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e86fffff920f43e2182c9548ac7e06e565317a23a7c9e8f5ddcafcff#256) ⟨k.val, by omega⟩)
      (0x61cdcc58#32, 0x24c303dc#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_20_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000004b89fff27870b3b68ef2fbdf9e61f284eaa5b5e0aced99ef7e09c64f#256) ⟨k.val, by omega⟩)
      (0x79aba8bc#32, 0x0f508670#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_20_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000020ac000044082b1147273925c8350c56b20622abac8336d059b00000#256) ⟨k.val, by omega⟩)
      (0x14518e53#32, 0xd20a7442#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_20_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000efc80000c907fd8d21d0eb2085592971642286c241b1f08b8ef00000#256) ⟨k.val, by omega⟩)
      (0xfead8154#32, 0x80354f5d#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_20_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a58c0000ef15c2addfb6d5fd67b0867a0a17225afcec1d790eb00000#256) ⟨k.val, by omega⟩)
      (0x6da1ff94#32, 0x190be3f3#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_20_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001c6fffffccf44cb09fc5a5dbb1c541958e3e1ab01e7b54e7307147ef#256) ⟨k.val, by omega⟩)
      (0xfdbbe478#32, 0x2d9adafa#32)
      (0x00100000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
