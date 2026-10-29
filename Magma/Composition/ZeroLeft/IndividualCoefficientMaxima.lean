module

public import Magma.Composition.ZeroLeft.ParityCompleteSlice
public import Magma.DDT.OneHot.Extrema.GlobalMaximum
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Sharp individual-coefficient maxima in the zero-left three-round slice

Fix right input difference one and left output difference zero. The exact
unit-input row peak is `2^29` for even first keys and `2^30` for odd first
keys. Explicit output differences attain both values; the odd-key maximizer
is uniquely the rotation of `0x00000007`.

For every fixed right output difference, the exact column maximum is this
row peak times the second-round DDT factor, with an explicit attaining left
input difference. At one-bit right outputs the sharp bounds are `2^58` and
`2^59` respectively. Second key zero and output bit 23 attain them for every
first and third key. The overall one-bit bound is therefore exactly `2^59`.

The three round keys are arbitrary independent words. Closed computations
inspect only the already certified 77-entry reference table.
-/

namespace Magma.ThreeRoundIndividualCoefficientMaxima

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OddUnitInput77
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.OneHotGlobalMaximum
open Magma.OneHotThreeRoundColumns

/-! ## 1. A small certified bound for the 77-entry odd reference table. -/

/-- Every stored count is at most 2^30; equality occurs at the
    single unrotated difference 0x00000007. -/
private theorem oddRows_entry_max_characterization :
    ∀ p ∈ oddRows,
      p.2 ≤ 2 ^ 30 ∧
        (p.2 = 2 ^ 30 ↔ p.1 = (0x00000007#32)) := by
  decide +kernel

/-- After applying the RFC eleven-bit rotation, the 77 target words
    remain pairwise distinct. This is only a 77-element check. -/
private theorem oddRows_rotated_unique :
    ∀ p ∈ oddRows, ∀ q ∈ oddRows,
      rot11 p.1 = rot11 q.1 → p = q := by
  decide +kernel

/-- An arbitrary lookup in the 77-entry table is either zero or comes
    from exactly one certified entry. -/
private theorem odd_reference_zero_or_single_entry (d : (V 32)) :
    oddReferenceCount d = 0 ∨
      ∃ p : (V 32) × Nat, p ∈ oddRows ∧
        rot11 p.1 = d ∧ oddReferenceCount d = p.2 := by
  classical
  let s : Finset ((V 32) × Nat) :=
    oddRows.toFinset.filter (fun p => rot11 p.1 = d)
  have hchange : oddReferenceCount d = ∑ p ∈ s, p.2 := rfl
  by_cases hs : s.Nonempty
  · obtain ⟨p, hp⟩ := hs
    have hpList : p ∈ oddRows :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hpd : rot11 p.1 = d := (Finset.mem_filter.mp hp).2
    have hsingle : s = {p} := by
      ext q
      constructor
      · intro hq
        have hqList : q ∈ oddRows :=
          List.mem_toFinset.mp (Finset.mem_filter.mp hq).1
        have hqd : rot11 q.1 = d := (Finset.mem_filter.mp hq).2
        exact Finset.mem_singleton.mpr
          (oddRows_rotated_unique q hqList p hpList (hqd.trans hpd.symm))
      · intro hq
        have heq : q = p := Finset.mem_singleton.mp hq
        exact heq ▸ hp
    right
    refine ⟨p, hpList, hpd, ?_⟩
    rw [hchange, hsingle]
    simp
  · have hempty : s = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      exact hs
    left
    rw [hchange, hempty]
    simp

/-- No odd-key output difference has more than 2^30 witnesses. -/
theorem odd_reference_le (d : (V 32)) :
    oddReferenceCount d ≤ 2 ^ 30 := by
  rcases odd_reference_zero_or_single_entry d with hzero | ⟨p, hp, _, hval⟩
  · rw [hzero]
    norm_num
  · rw [hval]
    exact (oddRows_entry_max_characterization p hp).1

/-- The largest odd-key coefficient is attained at this exact
    unrotated S-box difference, certified by the original 77-row table. -/
theorem odd_reference_peak :
    oddReferenceCount (rot11 (0x00000007#32)) = 2 ^ 30 := by
  decide +kernel

/-- In the odd reference row, the maximizing output is UNIQUE. -/
theorem odd_reference_eq_peak_iff (d : (V 32)) :
    oddReferenceCount d = 2 ^ 30 ↔
      d = rot11 (0x00000007#32) := by
  constructor
  · intro hd
    rcases odd_reference_zero_or_single_entry d with hz | ⟨p, hp, hrot, hval⟩
    · rw [hz] at hd
      norm_num at hd
    · have hmax : p.2 = 2 ^ 30 := by
        rw [hval] at hd
        exact hd
      have hword := (oddRows_entry_max_characterization p hp).2.mp hmax
      rw [hword] at hrot
      exact hrot.symm
  · intro hd
    rw [hd]
    exact odd_reference_peak

/-! ## 2. The exact maximum of the entire first-round DDT row. -/

/-- Maximum first-factor count selected by the parity of k0. -/
def rowPeak (k₀ : (V 32)) : Nat :=
  if k₀.toNat % 2 = 0 then 2 ^ 29 else 2 ^ 30

/-- An explicit output difference attaining the maximum at every k0. -/
def rowPeakWitness (k₀ : (V 32)) : (V 32) :=
  if k₀.toNat % 2 = 0 then
    0x00001000#32
  else
    rot11 (0x00000007#32)

/-- The *actual* first-round DDT is bounded, for all 2^32 outputs,
    using only the certified eight-entry and 77-entry reference descriptions. -/
theorem one_round_row_upper (k₀ d : (V 32)) :
    xorDDT_g k₀ (1#32) d ≤ rowPeak k₀ := by
  rw [one_round_unit_exact]
  by_cases hk : k₀.toNat % 2 = 0
  · simp only [parityRowCount, rowPeak, hk, ite_true]
    by_cases hd : d ∈ eightOffsets <;> simp [hd]
  · simpa only [parityRowCount, rowPeak, hk, ite_false] using
      odd_reference_le d

/-- For every first round key, the upper bound is truly attained. -/
theorem one_round_row_peak_attained (k₀ : (V 32)) :
    xorDDT_g k₀ (1#32) (rowPeakWitness k₀) = rowPeak k₀ := by
  rw [one_round_unit_exact]
  by_cases hk : k₀.toNat % 2 = 0
  · have hmem : (0x00001000#32) ∈ eightOffsets := by decide
    simp [parityRowCount, rowPeakWitness, rowPeak, hk, hmem]
  · simpa [parityRowCount, rowPeakWitness, rowPeak, hk] using
      odd_reference_peak

/-- In the odd-key case, the unique maximizing output difference is
    the rotation of 0x00000007. -/
theorem odd_key_first_row_peak_iff (k₀ d : (V 32))
    (hk : k₀.toNat % 2 = 1) :
    xorDDT_g k₀ (1#32) d = 2 ^ 30 ↔
      d = rot11 (0x00000007#32) := by
  rw [one_round_unit_exact]
  have hnot : ¬ k₀.toNat % 2 = 0 := by omega
  simp only [parityRowCount, hnot, ite_false]
  exact odd_reference_eq_peak_iff d

/-! ## 3. Sharp maximum of a whole column: for ARBITRARY bR. -/

private theorem xor_translate_cancel (x y : (V 32)) : xor x (xor x y) = y := by
  change x ^^^ (x ^^^ y) = y
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Universal upper bound for a SINGLE entry, no restriction on bR. -/
theorem each_coefficient_le_column_peak
    (k₀ k₁ k₂ aL bR : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR) ≤
      rowPeak k₀ * xorDDT_g k₁ bR (1#32) := by
  rw [every_three_round_entry_exact]
  exact Nat.mul_le_mul_right _
    (by simpa only [one_round_unit_exact] using
      one_round_row_upper k₀ (xor bR aL))

/-- Explicitly exhibit aL attaining this column's exact upper bound,
    even when the entire column is empty. -/
theorem coefficient_attains_column_peak
    (k₀ k₁ k₂ bR : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (xor bR (rowPeakWitness k₀), 1#32) (0#32, bR) =
      rowPeak k₀ * xorDDT_g k₁ bR (1#32) := by
  rw [every_three_round_entry_exact, xor_translate_cancel]
  rw [← one_round_unit_exact]
  exact congrArg (fun x : Nat => x * xorDDT_g k₁ bR (1#32))
    (one_round_row_peak_attained k₀)

/-- MAIN UNCONDITIONAL COLUMN MAXIMUM. This is a genuine maximum of
    actual DDT coefficients, not merely a bound on their sum. -/
theorem every_column_exact_maximum (k₀ k₁ k₂ bR : (V 32)) :
    (∀ aL : (V 32),
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
          (aL, 1#32) (0#32, bR) ≤
        rowPeak k₀ * xorDDT_g k₁ bR (1#32)) ∧
    (∃ aL : (V 32),
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
          (aL, 1#32) (0#32, bR) =
        rowPeak k₀ * xorDDT_g k₁ bR (1#32)) := by
  exact ⟨fun aL => each_coefficient_le_column_peak k₀ k₁ k₂ aL bR,
    ⟨xor bR (rowPeakWitness k₀),
      coefficient_attains_column_peak k₀ k₁ k₂ bR⟩⟩

/-! ## 4. SHARP global one-hot bounds of 2^58 and 2^59. -/

/-- No single one-hot column entry can exceed the parity-dependent
    bound, for any three round keys and any aL or output bit. -/
theorem onehot_single_entry_upper
    (k₀ k₁ k₂ aL : (V 32)) (j : Fin 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) ≤
      if k₀.toNat % 2 = 0 then 2 ^ 58 else 2 ^ 59 := by
  have hcolumn :=
    each_coefficient_le_column_peak k₀ k₁ k₂ aL (bitOutput j)
  have hsecond : xorDDT_g k₁ (bitOutput j) (1#32) ≤ 2 ^ 29 :=
    every_oneHot_DDT_le k₁ j
  have hproduct := Nat.mul_le_mul_left (rowPeak k₀) hsecond
  have hbound := Nat.le_trans hcolumn hproduct
  by_cases hk : k₀.toNat % 2 = 0
  · have hpower : 2 ^ 29 * 2 ^ 29 = 2 ^ 58 := by norm_num
    simpa only [rowPeak, hk, ite_true, hpower] using hbound
  · have hpower : 2 ^ 30 * 2 ^ 29 = 2 ^ 59 := by norm_num
    simpa only [rowPeak, hk, ite_false, hpower] using hbound

/-- These bounds are attained for EVERY first key of the specified
    parity and EVERY third key (taking second key zero and bit 23). -/
theorem onehot_single_entry_sharp
    (k₀ k₂ : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (xor (bitOutput (23 : Fin 32)) (rowPeakWitness k₀), 1#32)
      (0#32, bitOutput (23 : Fin 32)) =
      if k₀.toNat % 2 = 0 then 2 ^ 58 else 2 ^ 59 := by
  rw [coefficient_attains_column_peak]
  have hsecond : xorDDT_g (0#32) (bitOutput (23 : Fin 32)) (1#32) =
      2 ^ 29 := by
    simpa [bitOutput] using zero_key_bit23_attains_max
  rw [hsecond]
  by_cases hk : k₀.toNat % 2 = 0
  · have hpower : 2 ^ 29 * 2 ^ 29 = 2 ^ 58 := by norm_num
    simp only [rowPeak, hk, ite_true, hpower]
  · have hpower : 2 ^ 30 * 2 ^ 29 = 2 ^ 59 := by norm_num
    simp only [rowPeak, hk, ite_false, hpower]

/-- GLOBAL sharp maximum over all 32 one-hot right-output positions,
    all 2^96 independent round-key triples and all aL is 2^59.
    The parity-sensitive maximum for even k0 is 2^58. -/
theorem global_onehot_individual_maximum :
    (∀ k₀ k₁ k₂ aL : (V 32), ∀ j : Fin 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) ≤ 2 ^ 59) ∧
    (∃ k₀ k₁ k₂ aL : (V 32), ∃ j : Fin 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bitOutput j) = 2 ^ 59) := by
  constructor
  · intro k₀ k₁ k₂ aL j
    have h := onehot_single_entry_upper k₀ k₁ k₂ aL j
    split_ifs at h
    · omega
    · exact h
  · refine ⟨(1#32), (0#32), (0#32),
       xor (bitOutput (23 : Fin 32)) (rowPeakWitness (1#32)),
       (23 : Fin 32), ?_⟩
    have h := onehot_single_entry_sharp (1#32) (0#32)
    have hk : ¬ (1#32).toNat % 2 = 0 := by decide
    simpa only [hk, ite_false] using h

end Magma.ThreeRoundIndividualCoefficientMaxima
