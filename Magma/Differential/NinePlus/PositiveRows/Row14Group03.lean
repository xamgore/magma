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

/-- Kernel-checkable real RFC Magma trajectories: input bit 14,
    output bits 24..31. -/
theorem cell_14_24 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000045ae900091e2889315e39e6fbc7e052cd9e9db441466e4521c088008#256) ⟨k.val, by omega⟩)
      (0xe29f319a#32, 0x18273d7c#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x01000000#32) := by
  decide +kernel

theorem cell_14_25 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000219930c5b7c02454a7ef6d6ddb86fa20c205270f217cdc1650ed8f80#256) ⟨k.val, by omega⟩)
      (0x51c9b844#32, 0xb10c629a#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x02000000#32) := by
  decide +kernel

theorem cell_14_26 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a97a34c03b38e3255b91809e7fcbe2a2e9ade4cd53c9b13c0e366000#256) ⟨k.val, by omega⟩)
      (0x2dbf99d0#32, 0x03122aac#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x04000000#32) := by
  decide +kernel

theorem cell_14_27 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000010f8afffccbb351dbc86606fbe806b17c298c035a736c419b27c0030#256) ⟨k.val, by omega⟩)
      (0x8effe04c#32, 0xa2eda188#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x08000000#32) := by
  decide +kernel

theorem cell_14_28 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000006223b000cfcee20112ed9d1e9ed6bc40466ccbccfd07da8500108000#256) ⟨k.val, by omega⟩)
      (0xd518fb0c#32, 0x8a32334a#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x10000000#32) := by
  decide +kernel

theorem cell_14_29 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000a22943ff231deb61e8c0282998f5ed5d784c0abd3386398680e07c00#256) ⟨k.val, by omega⟩)
      (0xf50034c4#32, 0xa96a36da#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x20000000#32) := by
  decide +kernel

theorem cell_14_30 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000f5039fff21c76a95e9b5bc365dade5103e447ce3afb45dec2104d03c#256) ⟨k.val, by omega⟩)
      (0x973fda91#32, 0xed9363be#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x40000000#32) := by
  decide +kernel

theorem cell_14_31 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x0000000006182000df86a9de14834f8b66cb72fbe691bf259e8665704f25e377#256) ⟨k.val, by omega⟩)
      (0x57d2286d#32, 0xc0332ecf#32)
      (0x00004000#32, 0#32)
      = (0#32, 0x80000000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
