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

/-- Kernel-checkable real RFC Magma trajectories: input bit 8,
    output bits 0..7. -/
theorem cell_08_00 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000033e70eff404aa69d34aca51c2b11141b4a18d5f5bbda87e1581f4e23#256) ⟨k.val, by omega⟩)
      (0x40885fbf#32, 0xdb838e85#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000001#32) := by
  decide +kernel

theorem cell_08_01 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000b511b0050ffc1bdfc4b0946200e966999bed48b69a2b807f1711db2#256) ⟨k.val, by omega⟩)
      (0x02ae4e22#32, 0x1ffd6e85#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000002#32) := by
  decide +kernel

theorem cell_08_02 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000081a28eff152093f095827a9b55764dc45e5c425cafcf24590ba0280c#256) ⟨k.val, by omega⟩)
      (0x51e2bf55#32, 0xd0406af7#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000004#32) := by
  decide +kernel

theorem cell_08_03 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000053ffb49f090350af36f0a63a403b58e51c7c140739140ef21a69df2a#256) ⟨k.val, by omega⟩)
      (0xf165b901#32, 0x5d40acc8#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000008#32) := by
  decide +kernel

theorem cell_08_04 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b56f02bab80910caba679a786012c89107be818596a30a162584aa4c#256) ⟨k.val, by omega⟩)
      (0xcd8deb64#32, 0xd3dfd153#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000010#32) := by
  decide +kernel

theorem cell_08_05 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000005a8fbf00d40dc0b6e9bfe0e769c9e789a3157846aee323b6ae8242d0#256) ⟨k.val, by omega⟩)
      (0xa6d9710e#32, 0x7c813222#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000020#32) := by
  decide +kernel

theorem cell_08_06 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000018e5f3c59d2aacfdb89a44ff6f663ac69e5a03513ddf3bae19ef2b8#256) ⟨k.val, by omega⟩)
      (0x0160daea#32, 0x5322d42e#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000040#32) := by
  decide +kernel

theorem cell_08_07 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000edd164ff3803a4bbae7a583b1e81080d32e42ad4b634c8feefc20570#256) ⟨k.val, by omega⟩)
      (0xa1913b19#32, 0x0339bdf1#32)
      (0x00000100#32, 0#32)
      = (0#32, 0x00000080#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
