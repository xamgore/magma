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

/-- Kernel-checkable real RFC Magma trajectories: input bit 16,
    output bits 16..23. -/
theorem cell_16_16 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000055affff709cf17678a493504a8f9a3ab6575a90ae81ccd2ebaacfff#256) ⟨k.val, by omega⟩)
      (0x5fe1358e#32, 0x5e56a319#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00010000#32) := by
  decide +kernel

theorem cell_16_17 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000d5b70080840951ca0533b9b10decbce3106211130ff60f45879dc000#256) ⟨k.val, by omega⟩)
      (0x4bfdbbaf#32, 0x2efa8e1d#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00020000#32) := by
  decide +kernel

theorem cell_16_18 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000ac2ffff75b30d81227b125738e9d54ac3b68d89805961f0bcec3f80#256) ⟨k.val, by omega⟩)
      (0x1abdd58f#32, 0xc4556f29#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00040000#32) := by
  decide +kernel

theorem cell_16_19 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b082b9a8e769f90b78078333fb1e277c000cc47c91025bd0e2b7ca00#256) ⟨k.val, by omega⟩)
      (0xb9b74613#32, 0xa5ad4d01#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00080000#32) := by
  decide +kernel

theorem cell_16_20 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000009962ffffe0bd147f059ff86453e599acd21a2f825eaa63ae7f71f80f#256) ⟨k.val, by omega⟩)
      (0x30701343#32, 0x3e4647c3#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00100000#32) := by
  decide +kernel

theorem cell_16_21 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000633c7fff9ef2d395fe7941ad0202cdf85c532504f4d6fb8a70f37fb8#256) ⟨k.val, by omega⟩)
      (0x7f6b9d09#32, 0xb406c2e6#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00200000#32) := by
  decide +kernel

theorem cell_16_22 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x00000000b7853fff202fe4a9dfa2cced74de7bd21223e4f7c73c3bd73da7bf20#256) ⟨k.val, by omega⟩)
      (0x7c1c4d26#32, 0xb9881cf8#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00400000#32) := by
  decide +kernel

theorem cell_16_23 :
    multiRoundDelta 9
      (fun k : Fin 9 => roundKey (0x000000000f54ff7ff6e10d01d7fbbde14d3ff637fc35ef430893aa124e47ffff#256) ⟨k.val, by omega⟩)
      (0xaf662d60#32, 0xde106d42#32)
      (0x00010000#32, 0#32)
      = (0#32, 0x00800000#32) := by
  decide +kernel

end Magma.DiffanNineRoundPositiveRows
