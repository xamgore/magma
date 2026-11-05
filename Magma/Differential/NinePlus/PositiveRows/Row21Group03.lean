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

/-- Kernel-checkable real RFC Magma trajectories: input bit 21,
    output bits 24..31. -/
theorem cell_21_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000093000000327fabf027100aa2b8505827a794ff77eec8c3ec5200000#256) ⟨k.val, by omega⟩)
      (0xcecc06ef#32, 0x747a9b07#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_21_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003eb0000022908ddc390c6ef075c330deb7efcb0d896f351dc22000d0#256) ⟨k.val, by omega⟩)
      (0xa226db65#32, 0x4d5ea35d#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_21_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000039d000008f3265f040e7abb922b1a5137cb80619d9daa9d149000000#256) ⟨k.val, by omega⟩)
      (0xb45b7a58#32, 0x142593cf#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_21_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f4700000fc47e2ce0d73c863a021f7c2b5a17e21fe045c7af7600000#256) ⟨k.val, by omega⟩)
      (0x53b22520#32, 0xb209aaa4#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_21_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000091200000ba9b25a17e9b826c44a46b7c1a94d0b3ab45bf1d74020000#256) ⟨k.val, by omega⟩)
      (0x359bca80#32, 0xfd727375#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_21_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f52000002ef36095ea4f97bb77a488387dc3365b53d79da7bc2b0000#256) ⟨k.val, by omega⟩)
      (0xf9c0216c#32, 0x9cbc4c84#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_21_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000961800008b1af4869a9afe4d479816c8a2f31fa740fba6bff0082000#256) ⟨k.val, by omega⟩)
      (0xefdd4756#32, 0xe8cf0bd0#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_21_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f9500000488fc785fe88793a72fa5b8dfda49cf49392b270875de5d3#256) ⟨k.val, by omega⟩)
      (0x73a7fb7b#32, 0xc3f6aea3#32)
      (0x00200000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
