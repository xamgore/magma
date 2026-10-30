module

import all Init.Data.Range.Basic
public import Magma.Diffan.ExactPositiveDefectMass

@[expose] public section

/-!
# Remaining exceptional prefixes at zero second round key

The odd-first-key zero-left analysis identified six potentially ambiguous
low-20 prefixes. `ExactPositiveDefectMass` settles 0xCE800, where three
intermediate differences contribute positive mass.

Here we fix the canonical input differences aL with their upper 12 bits
zero and examine the other five prefixes, under k1 = 0. We prove:
* aL = 0x4E800: exactly one compatible intermediate c=0x00300000,
  with weight 3*2^50, therefore zero coupling defect at this output;
* aL in {0xCE803,0xCE804,0xCE806,0xCE807}: no compatible c,
  so the full convolution, all D3 values and all defects are zero.

Both conclusions hold for every odd first key k0 and every third key k2.
The high 12 bits of aL are fixed here; no claim is made about arbitrary
aL sharing the same low-20 prefix.

The finite certificates identify two- and four-element candidate fibers
inside the certified odd-key support table. Algebraic sum identities then
give the complete convolution and coupling defect.
-/

namespace Magma.DiffanOtherExceptionalZeroSecond

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OddUnitInput77
open Magma.DiffanOddUnitLow20CollisionClasses
open Magma.DiffanExactPositiveDefectMass
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- Four canonical low-20 prefixes whose second-key-zero column is empty. -/
def deadCanonicalPrefixes : Finset Word :=
  {0x000CE803#32, 0x000CE804#32, 0x000CE806#32, 0x000CE807#32}

/-- All four share the same two *potential* intermediate differences. -/
private def deadCandidates : Finset Word :=
  {0x5BD00000#32, 0xDBD00000#32}

/-- Each of the four canonical prefixes has the same two-element
    candidate fiber in the certified odd-key support table. -/
private theorem dead_candidate_fiber (aL : Word)
    (h : aL ∈ deadCanonicalPrefixes) :
    oddPotentialCandidates aL = deadCandidates := by
  simp only [deadCanonicalPrefixes, Finset.mem_insert,
    Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> subst aL <;> decide +kernel

/-- Both potential column inputs are impossible for g[0] -> 1. -/
private theorem dead_candidate_column_zero (c : Word)
    (hc : c ∈ deadCandidates) :
    xorDDT_g (0#32) c (1#32) = 0 := by
  simp only [deadCandidates, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h <;> subst c <;>
    (rw [zeroKey_column_eq_local]; decide +kernel)

/-- For the four canonical prefixes the REAL support intersection is empty,
    uniformly over all odd first keys. -/
theorem dead_overlap_empty
    (k₀ aL : Word) (hk : k₀.toNat % 2 = 1)
    (ha : aL ∈ deadCanonicalPrefixes) :
    supportOverlap k₀ (0#32) aL (1#32) = ∅ := by
  apply Set.Subset.antisymm
  · intro c hc
    have hpotential := odd_overlap_subset_candidates k₀ (0#32) aL c hk hc
    rw [dead_candidate_fiber aL ha] at hpotential
    have hz := dead_candidate_column_zero c hpotential
    exact ((Nat.ne_of_gt hc.2) hz).elim
  · exact Set.empty_subset _

/-- Every requested three-round transition is impossible here. -/
theorem dead_threeRound_zero
    (k₀ k₂ aL requested : Word)
    (hk : k₀.toNat % 2 = 1)
    (ha : aL ∈ deadCanonicalPrefixes) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, requested) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have hc := (zeroLeftDDT_pos_iff_mem k₀ (0#32) k₂ aL
    (1#32) requested).mp hp
  rw [dead_overlap_empty k₀ aL hk ha] at hc
  exact hc

/-- The defect vanishes for EVERY requested output, not only positive DDT. -/
theorem dead_defect_zero
    (k₀ k₂ aL requested : Word)
    (hk : k₀.toNat % 2 = 1)
    (ha : aL ∈ deadCanonicalPrefixes) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) requested = 0 := by
  apply (couplingDefect_zero_iff_subset k₀ (0#32) k₂
    aL (1#32) requested).mpr
  rw [dead_overlap_empty k₀ aL hk ha]
  exact Set.empty_subset _

/-- The fifth remaining exceptional canonical prefix. -/
def oneAL : Word := 0x0004E800#32

def oneC : Word :=
  0x00300000#32

private def fourCandidates : Finset Word :=
  {0#32, 0x00300000#32, 0x00400000#32, 0x00500000#32}

/-- The full shifted odd first-round prefix fiber has four elements. -/
private theorem four_candidate_fiber :
    oddPotentialCandidates oneAL = fourCandidates := by
  decide +kernel

/-- Every other member of this four-element fiber has zero g[0] column
    coefficient. This is just three local 4-bit S-box checks. -/
private theorem other_three_column_zero (c : Word)
    (hc : c ∈ fourCandidates) (hne : c ≠ oneC) :
    xorDDT_g (0#32) c (1#32) = 0 := by
  simp only [fourCandidates, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with h | h | h | h
  · subst c
    rw [zeroKey_column_eq_local]
    decide +kernel
  · exact (hne h).elim
  · subst c
    rw [zeroKey_column_eq_local]
    decide +kernel
  · subst c
    rw [zeroKey_column_eq_local]
    decide +kernel

/-- The exact first factor follows from the certified 77-entry table;
    the second factor is the product of the eight 4-bit S-box DDTs. -/
theorem one_local_factors (k₀ : Word) (hk : k₀.toNat % 2 = 1) :
    xorDDT_g k₀ (1#32) (xor oneC oneAL) = 3 * 2 ^ 21 ∧
    xorDDT_g (0#32) oneC (1#32) = 2 ^ 29 := by
  constructor
  · rw [odd_key_complete_DDT k₀ _ hk]
    decide +kernel
  · rw [zeroKey_column_eq_local]
    decide +kernel

/-- The one supported product is exactly 3*2^50. -/
theorem one_overlapWeight_exact (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    overlapWeight k₀ (0#32) oneAL (1#32) oneC = 3 * 2 ^ 50 := by
  obtain ⟨hrow, hcol⟩ := one_local_factors k₀ hk
  simp only [overlapWeight, hrow, hcol]
  norm_num

/-- The real overlap contains exactly one candidate, not four. -/
theorem one_overlap_singleton (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    supportOverlap k₀ (0#32) oneAL (1#32) = ({oneC} : Set Word) := by
  have hweight := one_overlapWeight_exact k₀ hk
  have hone : oneC ∈ supportOverlap k₀ (0#32) oneAL (1#32) :=
    (overlapWeight_pos_iff k₀ (0#32) oneAL (1#32) oneC).mp
      (by rw [hweight]; norm_num)
  apply Set.Subset.antisymm
  · intro c hc
    have hpotential := odd_overlap_subset_candidates k₀ (0#32) oneAL c hk hc
    rw [four_candidate_fiber] at hpotential
    by_contra hne
    have hneq : c ≠ oneC := by
      simpa only [Set.mem_singleton_iff] using hne
    have hz := other_three_column_zero c hpotential hneq
    exact ((Nat.ne_of_gt hc.2) hz).elim
  · intro c hc
    have heq : c = oneC := Set.mem_singleton_iff.mp hc
    subst c
    exact hone

/-- All non-selected intermediate weights are zero. -/
private theorem one_other_weight_zero (k₀ c : Word)
    (hk : k₀.toNat % 2 = 1) (hne : c ≠ oneC) :
    overlapWeight k₀ (0#32) oneAL (1#32) c = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have hc := (overlapWeight_pos_iff k₀ (0#32) oneAL (1#32) c).mp hp
  rw [one_overlap_singleton k₀ hk] at hc
  exact hne (Set.mem_singleton_iff.mp hc)

/-- The entire 32-bit symbolic convolution has just one nonzero term. -/
theorem one_entire_convolution (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    (∑ c : Word, overlapWeight k₀ (0#32) oneAL (1#32) c) =
      3 * 2 ^ 50 := by
  classical
  have hsum :
      (∑ c : Word, overlapWeight k₀ (0#32) oneAL (1#32) c) =
        overlapWeight k₀ (0#32) oneAL (1#32) oneC := by
    exact Finset.sum_eq_single_of_mem oneC (Finset.mem_univ oneC)
      (fun c _ hne => one_other_weight_zero k₀ c hk hne)
  exact hsum.trans (one_overlapWeight_exact k₀ hk)

/-- Exact DDT for every requested bR, independently of the third key. -/
theorem one_selectedDDT_exact (k₀ k₂ requested : Word)
    (hk : k₀.toNat % 2 = 1) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (oneAL, 1#32) (0#32, requested) =
      if requested = oneC then 3 * 2 ^ 50 else 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  change overlapWeight k₀ (0#32) oneAL (1#32) requested = _
  by_cases heq : requested = oneC
  · subst requested
    simpa only [ite_true] using one_overlapWeight_exact k₀ hk
  · simp only [heq, ite_false]
    exact one_other_weight_zero k₀ requested hk heq

/-- Exact defect: zero on the only supported diagonal, 3*2^50 off it.
    This is the other positive-but-defect-free exceptional prefix. -/
theorem one_defect_exact (k₀ k₂ requested : Word)
    (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ oneAL (1#32) (0#32) requested =
      if requested = oneC then 0 else 3 * 2 ^ 50 := by
  by_cases heq : requested = oneC
  · subst requested
    simp only [ite_true]
    apply (couplingDefect_zero_iff_subset k₀ (0#32) k₂
      oneAL (1#32) oneC).mpr
    rw [one_overlap_singleton k₀ hk]
  · simp only [heq, ite_false]
    have hmem : oneC ∈ (Finset.univ : Finset Word).erase requested :=
      Finset.mem_erase.mpr ⟨Ne.symm heq, Finset.mem_univ oneC⟩
    have hsum : offDiagonalMass k₀ (0#32) oneAL (1#32) requested =
        overlapWeight k₀ (0#32) oneAL (1#32) oneC := by
      unfold offDiagonalMass
      exact Finset.sum_eq_single_of_mem oneC hmem
        (fun c _ hne => one_other_weight_zero k₀ c hk hne)
    calc
      couplingDefect k₀ (0#32) k₂ oneAL (1#32) (0#32) requested =
          offDiagonalMass k₀ (0#32) oneAL (1#32) requested :=
        couplingDefect_eq_offDiagonalMass
          k₀ (0#32) k₂ oneAL (1#32) requested
      _ = overlapWeight k₀ (0#32) oneAL (1#32) oneC := hsum
      _ = 3 * 2 ^ 50 := one_overlapWeight_exact k₀ hk

end Magma.DiffanOtherExceptionalZeroSecond
