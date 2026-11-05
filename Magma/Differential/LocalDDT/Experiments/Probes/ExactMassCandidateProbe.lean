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

private def smallCandidateCheck : Bool :=
  (oddPotentialCandidates witnessAL).toList.all (fun c =>
    decide (c ∈ activeThree ∨ localColumnCount c = 0))

set_option maxHeartbeats 5000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- The candidate fiber contains only the three positive local products. -/
private theorem smallCandidateCheck_true : smallCandidateCheck = true := by
  decide +kernel

/-- If a c belongs to the possible odd-key prefix fiber, then it is
    one of the three explicit witnesses or its SECOND DDT factor is zero. -/
private theorem candidate_or_column_zero (c : Word)
    (hc : c ∈ oddPotentialCandidates witnessAL) :
    c ∈ activeThree ∨ xorDDT_g (0#32) c (1#32) = 0 := by
  have h : c ∈ (oddPotentialCandidates witnessAL).toList := by
    simpa using hc
  have hh := (List.all_eq_true.mp smallCandidateCheck_true) c h
  rcases (of_decide_eq_true hh) with hm | hz
  · exact Or.inl hm
  · exact Or.inr ((zeroKey_column_eq_local c).trans hz)

/-- COMPLETENESS: no other intermediate difference survives both DDTs.
    For any odd first key, the actual support overlap is exactly the three
    certified words, not just known to contain them. -/
theorem overlap_iff_activeThree (k₀ c : Word)
    (hk : k₀.toNat % 2 = 1) :
    c ∈ supportOverlap k₀ (0#32) witnessAL (1#32) ↔
      c ∈ activeThree := by
  constructor
  · intro hc
    have hsmall := odd_overlap_subset_candidates
      k₀ (0#32) witnessAL c hk hc
    rcases candidate_or_column_zero c hsmall with hm | hz
    · exact hm
    · have hcpos := hc.2
      rw [hz] at hcpos
      omega
  · intro hm
    simp only [activeThree, Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨h0, h1, h2⟩ := odd_first_overlap_contains_three k₀ hk
    rcases hm with h | h | h
    · exact h ▸ h0
    · exact h ▸ h1
    · exact h ▸ h2

/-- Every weighted summand outside the three words is actually zero. -/
theorem overlapWeight_zero_outside (k₀ c : Word)
    (hk : k₀.toNat % 2 = 1)
    (hc : c ∉ activeThree) :
    overlapWeight k₀ (0#32) witnessAL (1#32) c = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have hs := (overlapWeight_pos_iff k₀ (0#32) witnessAL (1#32) c).mp hp
  exact hc ((overlap_iff_activeThree k₀ c hk).mp hs)


end Magma.DifanExactPositiveDefectMass
