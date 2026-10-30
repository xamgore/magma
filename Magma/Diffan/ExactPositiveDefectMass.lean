module

import all Init.Data.Range.Basic
public import Magma.Diffan.PositiveDefectConcreteWitness

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

namespace Magma.DiffanExactPositiveDefectMass

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OddUnitInput77
open Magma.DiffanPositiveDefectConcreteWitness
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanOddUnitLow20CollisionClasses
open Magma.DiffanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

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

private theorem smallCandidateCheck_true : smallCandidateCheck = true := by decide +kernel

/-- If a c belongs to the possible odd-key prefix fiber, then it is
    one of the three explicit witnesses or its SECOND DDT factor is zero. -/
private theorem candidate_or_column_zero (c : Word)
    (hc : c ∈ oddPotentialCandidates witnessAL) :
    c ∈ activeThree ∨ xorDDT_g (0#32) c (1#32) = 0 := by
  have hmem : c ∈ candidate29.toFinset := by
    rw [← candidate29_complete]
    exact hc
  have h : c ∈ candidate29 := List.mem_toFinset.mp hmem
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

/-- Exact convolution mass, independent of the odd first key. -/
theorem entire_convolution_exact (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    (∑ c : Word, overlapWeight k₀ (0#32) witnessAL (1#32) c) =
      49 * 2 ^ 46 := by
  classical
  have hsum := Finset.sum_subset
    (s₁ := activeThree) (s₂ := (Finset.univ : Finset Word))
    (f := overlapWeight k₀ (0#32) witnessAL (1#32))
    (by intro c _; exact Finset.mem_univ c)
    (by intro c _ hn; exact overlapWeight_zero_outside k₀ c hk hn)
  have hne0 : candidate0 ∉ ({candidate1, candidate2} : Finset Word) := by decide
  have hne1 : candidate1 ∉ ({candidate2} : Finset Word) := by decide
  have hw := three_weights_exact k₀ hk
  calc
    (∑ c : Word, overlapWeight k₀ (0#32) witnessAL (1#32) c) =
        ∑ c ∈ activeThree, overlapWeight k₀ (0#32) witnessAL (1#32) c :=
      hsum.symm
    _ = overlapWeight k₀ (0#32) witnessAL (1#32) candidate0 +
        overlapWeight k₀ (0#32) witnessAL (1#32) candidate1 +
        overlapWeight k₀ (0#32) witnessAL (1#32) candidate2 := by
      simp only [activeThree, Finset.sum_insert hne0, Finset.sum_insert hne1,
        Finset.sum_singleton, Nat.add_assoc]
    _ = 49 * 2 ^ 46 := by
      rw [hw.1, hw.2.1, hw.2.2]
      norm_num

/-- The exact defect is the full convolution mass minus the chosen
    diagonal term. This identity works for EVERY requested output. -/
theorem exact_defect_plus_selected_weight (k₀ k₂ requested : Word)
    (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ witnessAL (1#32)
      (0#32) requested +
    overlapWeight k₀ (0#32) witnessAL (1#32) requested =
      49 * 2 ^ 46 := by
  rw [couplingDefect_eq_offDiagonalMass]
  have hsplit :
      offDiagonalMass k₀ (0#32) witnessAL (1#32) requested +
        overlapWeight k₀ (0#32) witnessAL (1#32) requested =
        ∑ c : Word, overlapWeight k₀ (0#32) witnessAL (1#32) c := by
    change (∑ c ∈ (Finset.univ : Finset Word).erase requested,
      overlapWeight k₀ (0#32) witnessAL (1#32) c) +
      overlapWeight k₀ (0#32) witnessAL (1#32) requested = _
    exact Finset.sum_erase_add (Finset.univ : Finset Word)
      _ (Finset.mem_univ requested)
  exact hsplit.trans (entire_convolution_exact k₀ hk)

/-- At c0 the exact positive 3-round DDT is 2^50; the difference
    between total convolution and its diagonal term is 33*2^46. -/
theorem selected_ddt_and_exact_defect (k₀ k₂ : Word)
    (hk : k₀.toNat % 2 = 1) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (witnessAL, 1#32) (0#32, candidate0) = 2 ^ 50 ∧
    couplingDefect k₀ (0#32) k₂ witnessAL (1#32)
      (0#32) candidate0 = 33 * 2 ^ 46 := by
  have hterm := (three_weights_exact k₀ hk).1
  have hsum := exact_defect_plus_selected_weight k₀ k₂ candidate0 hk
  constructor
  · rw [xorDDT_rounds_three_zero_left_factorization]
    change overlapWeight k₀ (0#32) witnessAL (1#32) candidate0 = 2 ^ 50
    exact hterm
  · rw [hterm] at hsum
    have hnum : 33 * 2 ^ 46 + 2 ^ 50 = 49 * 2 ^ 46 := by norm_num
    omega

/-- The other two supported outputs have different exact defects;
    at any unsupported output the entire mass is off-diagonal. -/
theorem second_defect_exact (k₀ k₂ : Word)
    (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ witnessAL (1#32)
      (0#32) candidate1 = 17 * 2 ^ 46 := by
  have hsum := exact_defect_plus_selected_weight k₀ k₂ candidate1 hk
  rw [(three_weights_exact k₀ hk).2.1] at hsum
  have hnum : 17 * 2 ^ 46 + 2 ^ 51 = 49 * 2 ^ 46 := by norm_num
  omega

theorem third_defect_exact (k₀ k₂ : Word) (hk : k₀.toNat % 2 = 1) :
    couplingDefect k₀ (0#32) k₂ witnessAL (1#32) (0#32) candidate2 = 48 * 2 ^ 46 := by
  have hsum := exact_defect_plus_selected_weight k₀ k₂ candidate2 hk
  rw [(three_weights_exact k₀ hk).2.2] at hsum
  have hnum : 48 * 2 ^ 46 + 2 ^ 46 = 49 * 2 ^ 46 := by norm_num
  omega

private theorem eq_of_zero_summand {a b c : Nat} (h : a + b = c) (hb : b = 0) : a = c := by
  simpa only [hb, Nat.add_zero] using h

/-- Outside the exactly three supported outputs, there is no diagonal
    term and the whole 49·2^46 convolution mass is the defect. -/
theorem other_defect_exact (k₀ k₂ requested : Word)
    (hk : k₀.toNat % 2 = 1)
    (hnot : requested ∉ activeThree) :
    couplingDefect k₀ (0#32) k₂ witnessAL (1#32)
      (0#32) requested = 49 * 2 ^ 46 := by
  have hsum := exact_defect_plus_selected_weight k₀ k₂ requested hk
  exact eq_of_zero_summand hsum (overlapWeight_zero_outside k₀ requested hk hnot)

end Magma.DiffanExactPositiveDefectMass
