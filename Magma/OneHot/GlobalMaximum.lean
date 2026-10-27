module

public import Magma.OneHot.ExactCoefficientMasks
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact maxima and attaining key classes for the one-bit DDT slice

For output difference one and any one-bit input difference, the original
round-function DDT is at most `2^29` for every key. Key zero and input bit 23
attain this bound. The coefficient masks give all equality cases and classify
which keys admit at least one maximizing bit.

Writing `K` for the low twenty key bits and `q` for key nibble five, such a
bit exists exactly when `K = 0` and `q ≠ 8`, or when `K ≠ 0` and
`q ∉ {7, 8, 12, 13}`. Higher key bits are unrestricted.

The maximum aggregate mass of a zero-left three-round one-bit column is
`2^61`. A zero second-round key and output bit 23 attain it for every choice
of the first and third round keys. All bounds use the exact affine formulae
and structural exclusions, without enumerating full keys or input words.
-/

open scoped BigOperators

namespace Magma.OneHotGlobalMaximum

open Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotExactCoefficientMasks
open Magma.OneHotKeyClasses
open Magma.OneHotFullKeyClassInvariant
open Magma.OneHotThreeRoundColumns

private abbrev B : Nat :=
  2 ^ 20

private theorem lowKey_lt (k : V 32) : k.toNat % B < B := by exact Nat.mod_lt _ (by norm_num [B])

/-! ## 1. Pure arithmetic: a convex mixture of two Boolean coefficients. -/

/-- The weighted sum of two bits is at most the full prefix size. -/
private theorem weightedBits_le (N K u v : Nat)
    (hK : K < N) (hu : u < 2) (hv : v < 2) :
    (N - K) * u + K * v ≤ N := by
  have hu' : u = 0 ∨ u = 1 := by omega
  have hv' : v = 0 ∨ v = 1 := by omega
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
    subst u <;> subst v <;> simp <;> omega

/-- Equality in the weighted upper bound is completely characterized.
    Since K<N, a coefficient from carry-in zero must be present. -/
private theorem weightedBits_eq_iff (N K u v : Nat)
    (hK : K < N) (hu : u < 2) (hv : v < 2) :
    ((N - K) * u + K * v = N) ↔
      u = 1 ∧ (v = 1 ∨ K = 0) := by
  have hu' : u = 0 ∨ u = 1 := by omega
  have hv' : v = 0 ∨ v = 1 := by omega
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
    subst u <;> subst v <;> simp <;> omega

/-! ## 2. Exact bound and all equality cases for the active nibble. -/

/-- The one-round count never exceeds 2^29 at an active bit. -/
theorem active_DDT_le (k : V 32) (r : Fin 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) ≤ 2 ^ 29 := by
  rw [oneHot_g_DDT_exact_mask]
  have hw := weightedBits_le B (k.toNat % B)
    (coefficientBit (keyNibble5 k) r)
    (coefficientBit (nextNibble (keyNibble5 k)) r)
    (lowKey_lt k)
    (coefficientBit_lt_two _ _)
    (coefficientBit_lt_two _ _)
  calc
    2 ^ 9 * ((B - k.toNat % B) * coefficientBit (keyNibble5 k) r +
      (k.toNat % B) * coefficientBit (nextNibble (keyNibble5 k)) r)
        ≤ 2 ^ 9 * B := Nat.mul_le_mul_left _ hw
    _ = 2 ^ 29 := by norm_num [B]

/-- Exact characterization of equality at any of the four active bits. -/
theorem active_DDT_eq_max_iff (k : V 32) (r : Fin 4) :
    (xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) = 2 ^ 29) ↔
      coefficientBit (keyNibble5 k) r = 1 ∧
        (coefficientBit (nextNibble (keyNibble5 k)) r = 1 ∨
          k.toNat % B = 0) := by
  rw [oneHot_g_DDT_exact_mask]
  have hp : (2 ^ 29 : Nat) = 2 ^ 9 * B := by norm_num [B]
  rw [hp]
  have hscale (n : Nat) :
      (2 ^ 9 : Nat) * n = 2 ^ 9 * B ↔ n = B := by
    constructor
    · intro h
      norm_num [B] at h
      omega
    · intro h
      rw [h]
  exact (hscale _).trans
    (weightedBits_eq_iff B (k.toNat % B)
      (coefficientBit (keyNibble5 k) r)
      (coefficientBit (nextNibble (keyNibble5 k)) r)
      (lowKey_lt k)
      (coefficientBit_lt_two _ _)
      (coefficientBit_lt_two _ _))

/-! ## 3. The true bound holds for ALL 32 one-bit input positions. -/

/-- Global upper bound over every 32-bit key and one-hot input bit. -/
theorem every_oneHot_DDT_le (k : V 32) (j : Fin 32) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤ 2 ^ 29 := by
  by_cases hout : j.val < 20 ∨ 24 ≤ j.val
  · have hz := oneHot_outside_middle_zero k j hout
    change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 at hz
    simp [hz]
  · have hm : 20 ≤ j.val ∧ j.val < 24 := by omega
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j.val = 20 + r.val := by dsimp [r]; omega
    rw [hr]
    exact active_DDT_le k r

/-- ALL maximizers among the 32 positions: exact bit and key criterion. -/
theorem oneHot_DDT_eq_max_iff (k : V 32) (j : Fin 32) :
    (xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 29) ↔
      ∃ r : Fin 4,
        j.val = 20 + r.val ∧
        coefficientBit (keyNibble5 k) r = 1 ∧
          (coefficientBit (nextNibble (keyNibble5 k)) r = 1 ∨
            k.toNat % B = 0) := by
  constructor
  · intro hmax
    have hm : 20 ≤ j.val ∧ j.val < 24 := by
      by_contra hn
      have hout : j.val < 20 ∨ 24 ≤ j.val := by omega
      have hz := oneHot_outside_middle_zero k j hout
      change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 at hz
      rw [hz] at hmax
      norm_num at hmax
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j.val = 20 + r.val := by dsimp [r]; omega
    refine ⟨r, hr, ?_⟩
    apply (active_DDT_eq_max_iff k r).mp
    simpa only [← hr] using hmax
  · rintro ⟨r, hr, hbits⟩
    rw [hr]
    exact (active_DDT_eq_max_iff k r).mpr hbits

/-- The bound is sharp: zero round key and input bit 23 attain it. -/
theorem zero_key_bit23_attains_max :
    xorDDT_g (0#32) (BitVec.ofNat 32 (2 ^ 23)) (1#32) = 2 ^ 29 := by
  have h₀ : coefficientBit (keyNibble5 (0#32)) (3 : Fin 4) = 1 := by decide
  have hK : (0#32).toNat % B = 0 := by decide
  simpa using
    (active_DDT_eq_max_iff (0#32) (3 : Fin 4)).mpr ⟨h₀, Or.inr hK⟩

/-- The absolute one-round maximum is 2^29 and is attained, not merely
    an upper bound. Both quantifiers range over the full key/bit spaces. -/
theorem oneHot_global_max_exact :
    (∀ k : V 32, ∀ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤ 2 ^ 29) ∧
    (∃ k : V 32, ∃ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 29) := by
  refine ⟨every_oneHot_DDT_le, ?_⟩
  exact ⟨(0#32), (23 : Fin 32), zero_key_bit23_attains_max⟩

/-! ## 4. Which complete KEY classes admit some maximizing bit? -/

/-- A nibble's own support has at least one bit iff q is not 8. -/
private theorem some_mask_bit_iff (q : Fin 16) :
    (∃ r : Fin 4, coefficientBit q r = 1) ↔ q.val ≠ 8 := by
  fin_cases q <;> decide

/-- Consecutive nibble masks intersect exactly outside four exceptions. -/
private theorem common_mask_bit_iff (q : Fin 16) :
    (∃ r : Fin 4,
        coefficientBit q r = 1 ∧ coefficientBit (nextNibble q) r = 1) ↔
      q.val ≠ 7 ∧ q.val ≠ 8 ∧ q.val ≠ 12 ∧ q.val ≠ 13 := by
  fin_cases q <;> decide

/-- Exact classification of keys admitting at least ONE attaining input bit.
    Key bits above nibble 5 are unrestricted. -/
theorem key_has_maximizing_bit_iff (k : V 32) :
    (∃ j : Fin 32,
       xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 29) ↔
      (k.toNat % B = 0 ∧ (keyNibble5 k).val ≠ 8) ∨
      (k.toNat % B ≠ 0 ∧
        (keyNibble5 k).val ≠ 7 ∧
        (keyNibble5 k).val ≠ 8 ∧
        (keyNibble5 k).val ≠ 12 ∧
        (keyNibble5 k).val ≠ 13) := by
  constructor
  · rintro ⟨j, hmax⟩
    obtain ⟨r, _, h₀, h₁⟩ := (oneHot_DDT_eq_max_iff k j).mp hmax
    by_cases hK : k.toNat % B = 0
    · exact Or.inl ⟨hK,
        (some_mask_bit_iff (keyNibble5 k)).mp ⟨r, h₀⟩⟩
    · have hnext : coefficientBit (nextNibble (keyNibble5 k)) r = 1 := by
        rcases h₁ with h₁ | h₁
        · exact h₁
        · exact False.elim (hK h₁)
      exact Or.inr ⟨hK,
        (common_mask_bit_iff (keyNibble5 k)).mp ⟨r, h₀, hnext⟩⟩
  · rintro (⟨hK, hq⟩ | ⟨hK, hq⟩)
    · obtain ⟨r, h₀⟩ := (some_mask_bit_iff (keyNibble5 k)).mpr hq
      let j : Fin 32 := ⟨20 + r.val, by omega⟩
      refine ⟨j, (oneHot_DDT_eq_max_iff k j).mpr ?_⟩
      exact ⟨r, rfl, h₀, Or.inr hK⟩
    · obtain ⟨r, h₀, h₁⟩ := (common_mask_bit_iff (keyNibble5 k)).mpr hq
      let j : Fin 32 := ⟨20 + r.val, by omega⟩
      refine ⟨j, (oneHot_DDT_eq_max_iff k j).mpr ?_⟩
      exact ⟨r, rfl, h₀, Or.inl h₁⟩

/-! ## 5. Maximum three-round column mass. -/

/-- Mass of any of the four potentially nonzero columns is ≤ 2^61. -/
theorem three_round_column_mass_le
    (k₀ k₁ k₂ : V 32) (r : Fin 4) :
    (∑ aL : V 32,
       xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
         (aL, 1#32) (0#32,
           bitOutput (⟨20 + r.val, by omega⟩ : Fin 32))) ≤ 2 ^ 61 := by
  rw [oneHot_three_round_mass_exact_mask]
  have hw := weightedBits_le B (k₁.toNat % B)
    (coefficientBit (keyNibble5 k₁) r)
    (coefficientBit (nextNibble (keyNibble5 k₁)) r)
    (lowKey_lt k₁)
    (coefficientBit_lt_two _ _)
    (coefficientBit_lt_two _ _)
  calc
    2 ^ 41 * ((B - k₁.toNat % B) * coefficientBit (keyNibble5 k₁) r +
      (k₁.toNat % B) * coefficientBit (nextNibble (keyNibble5 k₁)) r)
        ≤ 2 ^ 41 * B := Nat.mul_le_mul_left _ hw
    _ = 2 ^ 61 := by norm_num [B]

/-- Zero second-round key and output bit 23 attain mass 2^61,
    for arbitrary outer round keys. -/
theorem three_round_max_attained
    (k₀ k₂ : V 32) :
    (∑ aL : V 32,
       xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
         (aL, 1#32) (0#32, bitOutput (23 : Fin 32))) = 2 ^ 61 := by
  have h₀ : coefficientBit (keyNibble5 (0#32)) (3 : Fin 4) = 1 := by decide
  have h₁ : coefficientBit (nextNibble (keyNibble5 (0#32))) (3 : Fin 4) = 1 := by decide
  rw [show bitOutput (23 : Fin 32) =
      bitOutput (⟨20 + (3 : Fin 4).val, by omega⟩ : Fin 32) by decide]
  rw [oneHot_three_round_mass_exact_mask, h₀, h₁]
  norm_num [B]

/-- The same 2^61 upper bound holds for ALL 32 one-hot output
    columns, not merely the four potentially nonzero columns. -/
theorem every_three_round_oneHot_column_mass_le
    (k₀ k₁ k₂ : V 32) (j : Fin 32) :
    (∑ aL : V 32,
       xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
         (aL, 1#32) (0#32, bitOutput j)) ≤ 2 ^ 61 := by
  by_cases hout : j.val < 20 ∨ 24 ≤ j.val
  · have hz := oneHot_outside_middle_zero k₁ j hout
    change xorDDT_g k₁ (bitOutput j) (1#32) = 0 at hz
    have hall :=
      (Magma.MultiRoundDDT.zeroLeft_column_empty_iff
        k₀ k₁ k₂ (1#32) (bitOutput j)).mpr hz
    simp [hall]
  · have hm : 20 ≤ j.val ∧ j.val < 24 := by omega
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j = (⟨20 + r.val, by omega⟩ : Fin 32) := by
      apply Fin.ext
      dsimp [r]
      omega
    rw [hr]
    exact three_round_column_mass_le k₀ k₁ k₂ r

/-- Sharp global upper bound for the 32 one-hot three-round column
    masses. The outer round keys do not affect the maximizer. -/
theorem three_round_oneHot_global_max_exact :
    (∀ k₀ k₁ k₂ : V 32, ∀ j : Fin 32,
      (∑ aL : V 32,
        xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
          (aL, 1#32) (0#32, bitOutput j)) ≤ 2 ^ 61) ∧
    (∀ k₀ k₂ : V 32,
      (∑ aL : V 32,
        xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
          (aL, 1#32) (0#32, bitOutput (23 : Fin 32))) = 2 ^ 61) := by
  exact ⟨every_three_round_oneHot_column_mass_le, three_round_max_attained⟩

end Magma.OneHotGlobalMaximum
