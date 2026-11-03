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

/-- Kernel-checkable real RFC Magma trajectories: input bit 5,
    output bits 24..31. -/
theorem cell_05_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009c87716fc7821fd7a248678687ebfadf7b41a093e7944fa84db8c01a#256) ⟨k.val, by omega⟩)
      (0x0405827d#32, 0xc8d1d55f#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_05_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006618ff5f99c4d71316621862831ced39427805c6f72815c51cfffe07#256) ⟨k.val, by omega⟩)
      (0xda10804c#32, 0x0da688fc#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_05_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a7de2f0ca2de276539533ef673c9c68fe4dd2e92664c22d7224bd138#256) ⟨k.val, by omega⟩)
      (0xeeb55f66#32, 0x94b8844f#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_05_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000665d6bef9c043cbf858091eb8a4d34ebb5d01519b2bff493ca4ffc0a#256) ⟨k.val, by omega⟩)
      (0xf0cb1e62#32, 0x80e29455#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_05_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a9cab15e18101afc521830543028ce9ae4d9825456d97bcea7a5f930#256) ⟨k.val, by omega⟩)
      (0xd7cb98ca#32, 0xd5ed12d4#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_05_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005377b4cfda8fb786c7235e2db6471687125310c872b974f1713383bf#256) ⟨k.val, by omega⟩)
      (0x0a655cd7#32, 0x970f4753#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_05_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5e67ecf7a11c098ee75b89c61f261aaf00886409707cc4fe7fffffc#256) ⟨k.val, by omega⟩)
      (0x694ef6b9#32, 0x9b037698#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_05_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000dd3b4a5c6097c9d07e9cd380a47b7aa6e4696c8804a7ee99faa35ea7#256) ⟨k.val, by omega⟩)
      (0xba5a6466#32, 0x719131d4#32)
      (0x00000020#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
