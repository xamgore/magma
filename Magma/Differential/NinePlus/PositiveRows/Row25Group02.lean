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

/-- Kernel-checkable real RFC Magma trajectories: input bit 25,
    output bits 16..23. -/
theorem cell_25_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000aa7fffff2fa15d24da1b5674737206b335f3ba32e8a943bfcf76ff89#256) ⟨k.val, by omega⟩)
      (0xc8a13045#32, 0xc4494391#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_25_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000097000000757f0368bc6e3f8682c7b702bb8d776e59b62cb4deee0000#256) ⟨k.val, by omega⟩)
      (0xb91f31cf#32, 0x6b9d7ee4#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_25_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000032000000b3119e40f2f7733b0fc933494ad19ee0fada652af5b1000d#256) ⟨k.val, by omega⟩)
      (0x4d3d6a10#32, 0xee0d8e06#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_25_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a9800000fff5342003d5ffd21e9c7363260bf155d1441921663b0000#256) ⟨k.val, by omega⟩)
      (0x10c54aed#32, 0xd0e8a591#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_25_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000bb000000e6fce3fc13c52fdbcf2bf05d1b69816ab0c0b8f0c9f00000#256) ⟨k.val, by omega⟩)
      (0x66462b16#32, 0x6b5f50cd#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_25_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000039800000e3fbc5086a1cab07b77ebba405d48f2458ed24f095700000#256) ⟨k.val, by omega⟩)
      (0x61635615#32, 0x2e9f4510#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_25_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000091c00000377a7a942085082048ed4c19890bcb2a60218dd5052e9e0b#256) ⟨k.val, by omega⟩)
      (0x1a5dcaf2#32, 0x75840bd4#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_25_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d5800000bc0c7e14706820f431f83f2dc1f820596f575a951e400000#256) ⟨k.val, by omega⟩)
      (0xc24c6583#32, 0xe6f0be5a#32)
      (0x02000000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
