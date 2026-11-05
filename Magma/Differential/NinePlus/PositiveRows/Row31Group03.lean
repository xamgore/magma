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

/-- Kernel-checkable real RFC Magma trajectories: input bit 31,
    output bits 24..31. -/
theorem cell_31_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000ccb00867838559aa6f7d41a8952e239c94003eb06d54549bc8e80080#256) ⟨k.val, by omega⟩)
      (0xb25201f7#32, 0xfa66c59a#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_31_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bc60af368c1de54567a45cb880853f176a7c1629c1cc788e9b001000#256) ⟨k.val, by omega⟩)
      (0x89d98859#32, 0xf23afbfd#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_31_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000036f8abdc1a52beb99d70597cf7ee5d62232850a54b3dcd2771000000#256) ⟨k.val, by omega⟩)
      (0x801fa241#32, 0xd1812684#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_31_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000e6a9f6c43e32cbcd76cda51c37f75700b7e529dc4fdb78f013800003#256) ⟨k.val, by omega⟩)
      (0xb5cb670b#32, 0xd01113c5#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_31_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000fada3d5fe4d454a011f003eb9b97c8fd2dfef64219300df4af000000#256) ⟨k.val, by omega⟩)
      (0x5cb48b53#32, 0x77c7cc7a#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_31_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000cd81e1b8fdbb073091192b79f7027f5c52e95f241d0aa20470003000#256) ⟨k.val, by omega⟩)
      (0x62b743e6#32, 0x1f689e90#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_31_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000003102880416c12ab901ebce9de4ef9a6bd5efcb7d595a2c0250002801#256) ⟨k.val, by omega⟩)
      (0xe278897f#32, 0xf1caf32b#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_31_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000049e14a798fe6b43085b79d9e25d84f409b37bcc2a264c1b021e467d4#256) ⟨k.val, by omega⟩)
      (0xda3ca607#32, 0x74f0ab8c#32)
      (0x80000000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DifanNineRoundPositiveRows
