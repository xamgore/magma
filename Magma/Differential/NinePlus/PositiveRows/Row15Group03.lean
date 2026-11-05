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

/-- Kernel-checkable real RFC Magma trajectories: input bit 15,
    output bits 24..31. -/
theorem cell_15_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000022b706a889d120918fc108e936948571382249746c5dd26493274f8#256) ⟨k.val, by omega⟩)
      (0x70936aac#32, 0x8fbd139b#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_15_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f7995fff8d0174e2b009514548c127d76b04aa6b63eb727a330d018c#256) ⟨k.val, by omega⟩)
      (0xa55ca79b#32, 0x2feaaa6f#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_15_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000008c5f2b3f8b3441869446e4283818c6c9f89ddd24f42bdc90913a407d#256) ⟨k.val, by omega⟩)
      (0xab007b39#32, 0x18ba3b81#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_15_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003c32dffffeb04972e74438f21b07eccf809d1e566108ed8f39203882#256) ⟨k.val, by omega⟩)
      (0x6e39102e#32, 0xfafc941f#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_15_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000001a48b000b879962e6176c3bce08073a6c737dbb964574d4850000000#256) ⟨k.val, by omega⟩)
      (0x106e53e8#32, 0x878ff023#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_15_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000c81e50000ae924fc48bcb0b2a5ccbcd6ed0e9b79b7b8830fc0000500#256) ⟨k.val, by omega⟩)
      (0xa865d942#32, 0x74cb3e40#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_15_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000071f6d000515cc8eb7ac59b0a39caabcee120eaf0712c2d60500e2000#256) ⟨k.val, by omega⟩)
      (0xb95ad569#32, 0x26c6d60e#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_15_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000095ecafffbf4b77624b437734789ddd1d9b93002c3f788ccfb0c865ac#256) ⟨k.val, by omega⟩)
      (0xfaa34fc5#32, 0x203b26ef#32)
      (0x00008000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
