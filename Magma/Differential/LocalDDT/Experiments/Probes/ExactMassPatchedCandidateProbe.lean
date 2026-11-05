module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.PositiveDefectConcreteWitness

@[expose] public section

/-!
# Exact three-round coupling mass at the exceptional prefix

On the already certified exceptional example (aL=0x000CE800, k1=0),
for any odd k0, the two-function convolution is supported at exactly
three intermediate differences. Their exact weights are 2^50, 2^51,
and 2^46. Consequently its total mass is 49*2^46, and the selected
bR=0x00300000 has exact defect 33*2^46.

The finite certificate checks the odd-row prefix fiber, containing at
most 29 candidates, through products of eight local S-box DDT entries.
-/

namespace Magma.DifanExactPositiveDefectMass

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OddUnitInput77
open Magma.DifanPositiveDefectConcreteWitness
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanOddUnitLow20CollisionClasses
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word := V 32

/-- Product of the eight local S-box DDT coefficients for output one. -/
def localColumnCount (c : Word) : Nat :=
  ∏ i : Fin 8,
    SBoxProperties.ddt i (wordDigits c i) (wordDigits (0x00200000#32) i)

/-- This pre-rotation output becomes 1 under the RFC 11-bit rotation. -/
private theorem rot_target : rot11 (0x00200000#32) = (1#32) := by decide

/-- Symbolic bridge, valid for *every* 32-bit input difference. -/
theorem zeroKey_column_eq_local (c : Word) :
    xorDDT_g (0#32) c (1#32) = localColumnCount c := by
  rw [← rot_target, xorDDT_g_zero_key_factor]
  rfl

/-- Each of the three supported column entries has count 2^29. -/
theorem three_column_exact :
    xorDDT_g (0#32) candidate0 (1#32) = 2 ^ 29 ∧
    xorDDT_g (0#32) candidate1 (1#32) = 2 ^ 29 ∧
    xorDDT_g (0#32) candidate2 (1#32) = 2 ^ 29 := by
  simp only [zeroKey_column_eq_local, localColumnCount]
  decide +kernel

/-- The certified complete odd row provides all three exact first
    factors, independent of the actual odd value of k0. -/
theorem three_row_exact (k₀ : Word) (hk : k₀.toNat % 2 = 1) :
    xorDDT_g k₀ (1#32) (xor candidate0 witnessAL) = 2 ^ 21 ∧
    xorDDT_g k₀ (1#32) (xor candidate1 witnessAL) = 2 ^ 22 ∧
    xorDDT_g k₀ (1#32) (xor candidate2 witnessAL) = 2 ^ 17 := by
  constructor
  · rw [odd_key_complete_DDT k₀ _ hk]
    decide +kernel
  constructor
  · rw [odd_key_complete_DDT k₀ _ hk]
    decide +kernel
  · rw [odd_key_complete_DDT k₀ _ hk]
    decide +kernel

/-- Quantitative first+second-row weights at three distinct c's. -/
theorem three_weights_exact (k₀ : Word) (hk : k₀.toNat % 2 = 1) :
    overlapWeight k₀ (0#32) witnessAL (1#32) candidate0 = 2 ^ 50 ∧
    overlapWeight k₀ (0#32) witnessAL (1#32) candidate1 = 2 ^ 51 ∧
    overlapWeight k₀ (0#32) witnessAL (1#32) candidate2 = 2 ^ 46 := by
  obtain ⟨hr0, hr1, hr2⟩ := three_row_exact k₀ hk
  obtain ⟨hc0, hc1, hc2⟩ := three_column_exact
  simp only [overlapWeight, hr0, hr1, hr2, hc0, hc1, hc2]
  norm_num

/-- The only possible nonzero contributions at the exceptional prefix.
    ALL other potential c values are already in the <=29-member set
    proved in `OddUnitLow20CollisionClasses`. -/
def activeThree : Finset Word := {candidate0, candidate1, candidate2}

/-- The 29 intermediate differences in the exceptional odd-row prefix fiber. -/
private def candidate29 : List Word := [
    0x00100000#32, 0x00200000#32, 0x00300000#32, 0x00600000#32,
    0x00700000#32, 0x00D00000#32, 0x01500000#32, 0x01D00000#32,
    0x02500000#32, 0x03500000#32, 0x03D00000#32, 0x04D00000#32,
    0x05500000#32, 0x05D00000#32, 0x06500000#32, 0x06D00000#32,
    0x07D00000#32, 0x13D00000#32, 0x2BD00000#32, 0x33D00000#32,
    0x3BD00000#32, 0x43D00000#32, 0x4BD00000#32, 0x53D00000#32,
    0x5BD00000#32, 0x6BD00000#32, 0x73D00000#32, 0x7BD00000#32,
    0xDBD00000#32
  ]

/-- The explicit candidate list represents the complete exceptional prefix fiber. -/
private theorem candidate29_complete :
    oddPotentialCandidates witnessAL = candidate29.toFinset := by
  decide +kernel

/-- Check which candidates have a positive product of local S-box DDT counts. -/
private def smallCandidateCheck : Bool :=
  candidate29.all (fun c =>
    decide (c ∈ activeThree ∨ localColumnCount c = 0))

set_option maxHeartbeats 5000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
private theorem smallCandidateCheck_true : smallCandidateCheck = true := by
  decide +kernel


end Magma.DifanExactPositiveDefectMass
