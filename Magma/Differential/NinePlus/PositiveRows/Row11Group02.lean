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

/-- Kernel-checkable real RFC Magma trajectories: input bit 11,
    output bits 16..23. -/
theorem cell_11_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b0c21c7dda32cf54dcd6067b031ef5371a33dc94175f7ccf16431f59#256) ⟨k.val, by omega⟩)
      (0x96b27652#32, 0xa441c9fd#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_11_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d4fc2f10abc0a81b145bcb90ba72ed5dbb2d8049103e1a74b455ebf7#256) ⟨k.val, by omega⟩)
      (0x60f2de29#32, 0x35a3c82f#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_11_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000073b62dc17e2d74d9bdcd1b426d3853307dfbf212ee3b28d805057600#256) ⟨k.val, by omega⟩)
      (0x3b834a35#32, 0xba8e6d63#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_11_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000770c880f4bd13d914c59be2fae24fac4b6cdaef39d05a1b3c49a91bd#256) ⟨k.val, by omega⟩)
      (0x2bec654b#32, 0x53bb719d#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_11_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000ce80eff0d831fee390b17e6148b96b0420f9d42ea628455913705c4#256) ⟨k.val, by omega⟩)
      (0x739b68d4#32, 0x019bf9b6#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_11_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bbf43300e016ba0bb0b8728c31bac65b0f4ff694f57772623f500000#256) ⟨k.val, by omega⟩)
      (0x1bae53ce#32, 0x3b876bc3#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_11_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000647ed4ff1bbf77b678e8ebe70cdd2d2a1aa8f5b6437f6ad3aadfff80#256) ⟨k.val, by omega⟩)
      (0xe6099205#32, 0x7921f98b#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_11_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000668b06fc9ec3bd3ab99ee101eadcd558d41ca286dafa253e23973000#256) ⟨k.val, by omega⟩)
      (0xd0c79221#32, 0xbfc7ce00#32)
      (0x00000800#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
