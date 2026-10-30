module

import all Init.Data.Range.Basic
public import Magma.Diffan.ExactPositiveDefectMass

@[expose] public section

/-!
# Exact eight-entry output-one DDT column of g[0]

This is a formula for ALL input differences c, not a scan over a
finite list of selected inputs. The existing `zeroKey_column_eq_local`
bridge factors the full 32-bit zero-key DDT into eight independent
four-bit RFC 8891 S-box DDTs.

The pre-rotation output difference 0x00200000 (which rotates to 1) has
nibble 5 equal to 2 and all other nibbles zero. Bijectivity of the
remaining seven S-boxes forces their input differences to zero. The
fifth-indexed S-box has precisely eight positive input differences,
with coefficient 2 each. Hence the full column is 2^29 at precisely
eight explicit words and zero everywhere else.

Consequences are exact for arbitrary first key k0, left input
difference aL, selected right output difference bR, and third key k2
when the second key is 0 and aR=1, bL=0. The full symbolic convolution
and defect become sums of at most eight coefficients of the first DDT.
-/

namespace Magma.DiffanZeroKeyEightColumn

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanExactPositiveDefectMass
open Magma.DiffanThreeRoundCouplingDefect
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

/-- The only 4-bit input differences of S-box 5 that can produce
    the pre-rotation output difference 2. -/
def allowedDigit5 : Finset (Fin 16) :=
  {3, 6, 8, 9, 10, 12, 13, 15}

/-- Reinsert one 4-bit digit into the 32-bit word at nibble position 5. -/
def digit5Word (a : Fin 16) : Word :=
  BitVec.ofNat 32 (a.val * 2 ^ 20)

/-- The exact eight-element zero-key output-one column support. -/
def zeroColumnSupport : Finset Word :=
  allowedDigit5.image digit5Word

/-- The support can also be read without decoding any nibble indices. -/
theorem zeroColumnSupport_eq_literals :
    zeroColumnSupport =
      ({0x00300000#32, 0x00600000#32,
        0x00800000#32, 0x00900000#32,
        0x00A00000#32, 0x00C00000#32,
        0x00D00000#32, 0x00F00000#32} : Finset Word) := by
  decide +kernel

/-- Each RFC S-box has sixteen zero-output transitions at input
    difference zero and none at other input differences. -/
private theorem sbox_zero_output (i : Fin 8) (a : Fin 16) :
    SBoxProperties.ddt i a 0 = if a = 0 then 16 else 0 := by
  fin_cases i <;> fin_cases a <;> decide +kernel

/-- The complete sixteen-entry DDT column (output 2) of S-box 5. -/
private theorem sbox_five_output_two (a : Fin 16) :
    SBoxProperties.ddt 5 a 2 =
      if a ∈ allowedDigit5 then 2 else 0 := by
  fin_cases a <;> decide +kernel

private theorem target_digit (i : Fin 8) :
    wordDigits (0x00200000#32) i = if i = 5 then 2 else 0 := by fin_cases i <;> decide

/-- A word with one embedded nibble has exactly the expected digits.
    All 16 * 8 cases are literal nibble extraction identities. -/
private theorem digit5Word_digits (a : Fin 16) (i : Fin 8) :
    wordDigits (digit5Word a) i =
      if i = 5 then a else 0 := by
  fin_cases a <;> fin_cases i <;> decide +kernel

private theorem digit5Word_injective : Function.Injective digit5Word := by
  intro a b h
  have hh := congrArg (fun c : Word => wordDigits c (5 : Fin 8)) h
  simpa [digit5Word_digits] using hh

/-- The column support has cardinality exactly 8, not merely at most 8. -/
theorem zeroColumnSupport_card : zeroColumnSupport.card = 8 := by
  rw [zeroColumnSupport, Finset.card_image_of_injective _ digit5Word_injective]
  decide

/-- A structural characterization of the eight words: all other input
    nibbles are zero, and nibble 5 is one of the eight allowed values. -/
private theorem digits_iff_zeroColumnSupport (c : Word) :
    ((∀ i : Fin 8, i ≠ 5 → wordDigits c i = 0) ∧
      wordDigits c 5 ∈ allowedDigit5) ↔
      c ∈ zeroColumnSupport := by
  constructor
  · rintro ⟨hz, h5⟩
    apply Finset.mem_image.mpr
    refine ⟨wordDigits c 5, h5, ?_⟩
    apply wordDigitsEquiv.injective
    funext i
    change wordDigits (digit5Word (wordDigits c 5)) i = wordDigits c i
    rw [digit5Word_digits]
    by_cases hi : i = 5
    · subst i
      simp
    · simp only [ite_eq_right hi]
      exact (hz i hi).symm
  · intro h
    obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp h
    have hc : c = digit5Word a := hca.symm
    subst c
    constructor
    · intro i hi
      rw [digit5Word_digits, ite_eq_right hi]
    · simpa [digit5Word_digits] using ha

/-- A zero local S-box factor makes the column-count product zero. -/
private theorem column_zero_of_factor (c : Word) (i : Fin 8)
    (hz : SBoxProperties.ddt i (wordDigits c i)
      (wordDigits (0x00200000#32) i) = 0) :
    localColumnCount c = 0 := by
  unfold localColumnCount
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

/-- Every positive support word has exactly the same local product. -/
private theorem localColumnCount_on_support (c : Word)
    (hc : c ∈ zeroColumnSupport) :
    localColumnCount c = 2 ^ 29 := by
  obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp hc
  have h : c = digit5Word a := hca.symm
  subst c
  unfold localColumnCount
  rw [Fin.prod_univ_eight]
  simp only [digit5Word_digits, target_digit]
  simp [sbox_zero_output, sbox_five_output_two, ha]

/-- Conversely, everything outside the eight-element support has a
    zero local S-box factor and hence a zero product. -/
private theorem localColumnCount_off_support (c : Word)
    (hc : c ∉ zeroColumnSupport) :
    localColumnCount c = 0 := by
  classical
  have hnot : ¬ ((∀ i : Fin 8, i ≠ 5 → wordDigits c i = 0) ∧
        wordDigits c 5 ∈ allowedDigit5) := by
    intro h
    exact hc ((digits_iff_zeroColumnSupport c).mp h)
  by_cases h5 : wordDigits c 5 ∈ allowedDigit5
  · have hex : ∃ i : Fin 8, i ≠ 5 ∧ wordDigits c i ≠ 0 := by
      by_contra hn
      apply hnot
      constructor
      · intro i hi
        by_contra hz
        exact hn ⟨i, hi, hz⟩
      · exact h5
    obtain ⟨i, hi, hne⟩ := hex
    apply column_zero_of_factor c i
    rw [target_digit, ite_eq_right hi, sbox_zero_output]
    simp [hne]
  · apply column_zero_of_factor c 5
    rw [target_digit, ite_eq_left rfl, sbox_five_output_two]
    simp [h5]

/-- For every 32-bit input difference c, the true
    zero-key g-function DDT column at output 1 has precisely eight
    positive entries, each of multiplicity 2^29. -/
theorem zeroKey_outputOne_exact (c : Word) :
    xorDDT_g (0#32) c (1#32) =
      if c ∈ zeroColumnSupport then 2 ^ 29 else 0 := by
  rw [zeroKey_column_eq_local]
  by_cases h : c ∈ zeroColumnSupport
  · rw [ite_eq_left h]
    exact localColumnCount_on_support c h
  · rw [ite_eq_right h]
    exact localColumnCount_off_support c h

/-- The exact positive support iff, without any hypothesis on c. -/
theorem zeroKey_outputOne_positive_iff (c : Word) :
    0 < xorDDT_g (0#32) c (1#32) ↔
      c ∈ zeroColumnSupport := by
  rw [zeroKey_outputOne_exact]
  by_cases hc : c ∈ zeroColumnSupport <;> simp [hc]

/-- The genuine overlap for ANY first key and ANY left input difference
    is an intersection of the first-round row with just eight fixed c's. -/
theorem overlap_zeroKeySecond_iff (k₀ aL c : Word) :
    c ∈ supportOverlap k₀ (0#32) aL (1#32) ↔
      c ∈ zeroColumnSupport ∧
        0 < xorDDT_g k₀ (1#32) (xor c aL) := by
  change (0 < xorDDT_g k₀ (1#32) (xor c aL) ∧
    0 < xorDDT_g (0#32) c (1#32)) ↔ _
  rw [zeroKey_outputOne_positive_iff]
  exact and_comm

/-- Exact contribution of each possible intermediate difference. -/
theorem overlapWeight_zeroKeySecond_exact (k₀ aL c : Word) :
    overlapWeight k₀ (0#32) aL (1#32) c =
      if c ∈ zeroColumnSupport then
        2 ^ 29 * xorDDT_g k₀ (1#32) (xor c aL)
      else 0 := by
  unfold overlapWeight
  rw [zeroKey_outputOne_exact]
  by_cases hc : c ∈ zeroColumnSupport
  · simp only [hc, ite_true]
    exact Nat.mul_comm _ _
  · simp only [hc, ite_false, Nat.mul_zero]

/-- The complete symbolic convolution reduces from 2^32 potential
    intermediate differences to the eight fixed members of C. -/
theorem fullConvolution_eight (k₀ aL : Word) :
    (∑ c : Word, overlapWeight k₀ (0#32) aL (1#32) c) =
      ∑ c ∈ zeroColumnSupport,
        2 ^ 29 * xorDDT_g k₀ (1#32) (xor c aL) := by
  classical
  have hs :
      (∑ c ∈ zeroColumnSupport, overlapWeight k₀ (0#32) aL (1#32) c) =
        ∑ c : Word, overlapWeight k₀ (0#32) aL (1#32) c := by
    apply Finset.sum_subset
    · intro c _
      exact Finset.mem_univ c
    · intro c _ hc
      rw [overlapWeight_zeroKeySecond_exact, ite_eq_right hc]
  calc
    _ = ∑ c ∈ zeroColumnSupport, overlapWeight k₀ (0#32) aL (1#32) c := hs.symm
    _ = ∑ c ∈ zeroColumnSupport,
          2 ^ 29 * xorDDT_g k₀ (1#32) (xor c aL) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [overlapWeight_zeroKeySecond_exact, ite_eq_left hc]

/-- A fully closed eight-term convolution formula: each remaining
    coefficient of the first DDT is already known by its key parity,
    through the previously proved eight-entry and 77-entry reference tables. -/
theorem fullConvolution_eight_parity (k₀ aL : Word) :
    (∑ c : Word, overlapWeight k₀ (0#32) aL (1#32) c) =
      ∑ c ∈ zeroColumnSupport,
        2 ^ 29 * parityRowCount k₀ (xor c aL) := by
  rw [fullConvolution_eight]
  apply Finset.sum_congr rfl
  intro c _
  rw [one_round_unit_exact]

/-- A compact finite set of exactly the surviving c values. -/
def survivingCandidates (k₀ aL : Word) : Finset Word :=
  zeroColumnSupport.filter
    (fun c => 0 < parityRowCount k₀ (xor c aL))

theorem survivingCandidates_iff_overlap (k₀ aL c : Word) :
    c ∈ survivingCandidates k₀ aL ↔ c ∈ supportOverlap k₀ (0#32) aL (1#32) := by
  rw [overlap_zeroKeySecond_iff]
  simp only [survivingCandidates, Finset.mem_filter]
  rw [one_round_unit_exact]

/-- At most eight intermediate differences survive for EVERY aL and k0.
    This is a genuine global upper bound on support intersection. -/
theorem survivingCandidates_card_le_eight (k₀ aL : Word) :
    (survivingCandidates k₀ aL).card ≤ 8 := by
  calc
    (survivingCandidates k₀ aL).card ≤ zeroColumnSupport.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 8 := zeroColumnSupport_card

/-- The selected three-round DDT coefficient is a single term of the
    same exact eight-entry table. It is still exact for every third key. -/
theorem threeRound_zeroLeft_eight (k₀ k₂ aL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, bR) =
      if bR ∈ zeroColumnSupport then
        2 ^ 29 * xorDDT_g k₀ (1#32) (xor bR aL)
      else 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  change overlapWeight k₀ (0#32) aL (1#32) bR = _
  exact overlapWeight_zeroKeySecond_exact k₀ aL bR

/-- Stronger exact defect formula: sum of just the seven or eight
    candidates other than the selected bR (rather than a 2^32 sum).
    The Finset erase removes bR only when it actually belongs to C. -/
theorem couplingDefect_eight (k₀ k₂ aL bR : Word) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR =
      ∑ c ∈ zeroColumnSupport.erase bR,
        2 ^ 29 * xorDDT_g k₀ (1#32) (xor c aL) := by
  classical
  rw [couplingDefect_eq_offDiagonalMass]
  unfold offDiagonalMass
  have hs :
      (∑ c ∈ zeroColumnSupport.erase bR,
        overlapWeight k₀ (0#32) aL (1#32) c) =
      ∑ c ∈ (Finset.univ : Finset Word).erase bR,
        overlapWeight k₀ (0#32) aL (1#32) c := by
    apply Finset.sum_subset
    · intro c hc
      have he := Finset.mem_erase.mp hc
      exact Finset.mem_erase.mpr ⟨he.1, Finset.mem_univ _⟩
    · intro c hc hnot
      have he := Finset.mem_erase.mp hc
      have hnone : c ∉ zeroColumnSupport := by
        intro hm
        exact hnot (Finset.mem_erase.mpr ⟨he.1, hm⟩)
      rw [overlapWeight_zeroKeySecond_exact, ite_eq_right hnone]
  calc
    _ = ∑ c ∈ zeroColumnSupport.erase bR,
          overlapWeight k₀ (0#32) aL (1#32) c := hs.symm
    _ = ∑ c ∈ zeroColumnSupport.erase bR,
          2 ^ 29 * xorDDT_g k₀ (1#32) (xor c aL) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [overlapWeight_zeroKeySecond_exact,
        ite_eq_left (Finset.mem_erase.mp hc).2]

/-- The defect too becomes a completely explicit sum of at most eight
    stored parity-row coefficients. Nothing remains to be inferred by
    treating the 32-bit intermediate differences as independent. -/
theorem couplingDefect_eight_parity (k₀ k₂ aL bR : Word) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR =
      ∑ c ∈ zeroColumnSupport.erase bR,
        2 ^ 29 * parityRowCount k₀ (xor c aL) := by
  rw [couplingDefect_eight]
  apply Finset.sum_congr rfl
  intro c _
  rw [one_round_unit_exact]

end Magma.DiffanZeroKeyEightColumn
