module
import all Init.Data.Range.Basic
public import Magma.Differential.NinePlus.SparseRoundWitnessSteps
public import Magma.Differential.FiveRounds.FiveRoundDDTReverse

set_option maxRecDepth 4096

@[expose] public section

/-!
# Actual positive five-round Magma differential certificates

Two SAT-discovered concrete trajectories were independently recomputed
in Python and are now checked by the Lean kernel as twenty independent
one-round equations. The positive DDT theorems use only those checked
equations, without computing a 64-bit DDT by brute force.
-/

namespace Magma.DiffanSparsePositiveWitnesses

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect
open Magma.DiffanFiveRoundDDTReverse
open Magma.DiffanSparseRoundSteps

private abbrev Word :=
  V 32

theorem ddt_pos_of_concrete_base (k₀ k₁ k₂ k₃ k₄ : Word) (a b p : FeistelState)
    (h : multiRoundDelta 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) p a = b) :
    0 < xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) a b := by
  unfold xorDDT_rounds
  apply Finset.card_pos.mpr
  refine ⟨p, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem delta_80000080_to_20200020 :
    multiRoundDelta 5 (fiveRoundKeys (0#32) (0xb3900250#32) (0xddfc38c3#32) (0xca24f050#32) (0#32))
        (0x9d651eb2#32, 0x17714960#32) (0x80000080#32, 0#32) =
      (0#32, 0x20200020#32) := by
  unfold multiRoundDelta
  have hx :
    stateXor (0x9d651eb2#32, 0x17714960#32) (0x80000080#32, 0#32) =
      (0x1d651e32#32, 0x17714960#32) := by
    decide +kernel
  rw [hx, w0_xor_five, w0_base_five]
  decide +kernel

theorem positive_80000080_to_20200020 :
    0 <
      xorDDT_rounds 5 (fiveRoundKeys (0#32) (0xb3900250#32) (0xddfc38c3#32) (0xca24f050#32) (0#32))
        (0x80000080#32, 0#32) (0#32, 0x20200020#32) :=
  ddt_pos_of_concrete_base _ _ _ _ _ _ _ _ delta_80000080_to_20200020

theorem delta_80000080_to_20400020 :
    multiRoundDelta 5 (fiveRoundKeys (0#32) (0x298d60a0#32) (0xe12d7fef#32) (0xae618a91#32) (0#32))
        (0x5ecd63c0#32, 0xc5b62afe#32) (0x80000080#32, 0#32) =
      (0#32, 0x20400020#32) := by
  unfold multiRoundDelta
  have hx :
    stateXor (0x5ecd63c0#32, 0xc5b62afe#32) (0x80000080#32, 0#32) =
      (0xdecd6340#32, 0xc5b62afe#32) := by
    decide +kernel
  rw [hx, w1_xor_five, w1_base_five]
  decide +kernel

theorem positive_80000080_to_20400020 :
    0 <
      xorDDT_rounds 5 (fiveRoundKeys (0#32) (0x298d60a0#32) (0xe12d7fef#32) (0xae618a91#32) (0#32))
        (0x80000080#32, 0#32) (0#32, 0x20400020#32) :=
  ddt_pos_of_concrete_base _ _ _ _ _ _ _ _ delta_80000080_to_20400020

theorem positive_reverse_20200020_to_80000080 :
    0 <
      xorDDT_rounds 5 (fiveRoundKeys (0#32) (0xca24f050#32) (0xddfc38c3#32) (0xb3900250#32) (0#32))
        (0x20200020#32, 0#32) (0#32, 0x80000080#32) := by
  rw [←
    outer_ddt_reverse (0#32) (0xb3900250#32) (0xddfc38c3#32) (0xca24f050#32) (0#32) (0x80000080#32)
      (0x20200020#32)]
  exact positive_80000080_to_20200020

theorem positive_reverse_20400020_to_80000080 :
    0 <
      xorDDT_rounds 5 (fiveRoundKeys (0#32) (0xae618a91#32) (0xe12d7fef#32) (0x298d60a0#32) (0#32))
        (0x20400020#32, 0#32) (0#32, 0x80000080#32) := by
  rw [←
    outer_ddt_reverse (0#32) (0x298d60a0#32) (0xe12d7fef#32) (0xae618a91#32) (0#32) (0x80000080#32)
      (0x20400020#32)]
  exact positive_80000080_to_20400020

end Magma.DiffanSparsePositiveWitnesses
