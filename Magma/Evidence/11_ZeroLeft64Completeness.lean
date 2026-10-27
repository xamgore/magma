module

public import Magma.Evidence.«10_ZeroLeft64ExactCounts»
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 11: completeness of the 64-pair zero-left slice

Fix the first two keys to zero, the input right difference to one, and the
output left difference to zero. Iteration 10 certified 64 distinct pairs
`(aL, bR)`, each with DDT count `2^58`, uniformly over the third key.

The total mass of this slice is exactly `2^64`. This follows from the row and
column conservation laws of the round-function DDT, using bijectivity of `g`
and XOR translations. Those reusable laws live in `Magma.CarryAutomaton`.
All sums are handled symbolically; no 32-bit or 64-bit universe is enumerated.

The 64 certified pairs exhaust the mass: `64 * 2^58 = 2^64`. Nonnegativity
forces every unlisted entry to zero. The resulting exact classification is
`DDT₃((aL, 1), (0, bR)) = if (aL, bR) ∈ predictedPairs then 2^58 else 0`,
for every third key. Positive support is therefore exactly the earlier list.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.Evidence.ZeroLeftSupport Magma.Evidence.ZeroLeft64Exact

namespace Magma.Evidence.ZeroLeft64Completeness

/-! ### The total weight of the zero-left DDT slice -/

def zeroLeftSlice (k₂ : V 32) (p : FeistelState) : Nat :=
  xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
    (p.1, 1#32) (0#32, p.2)

/-- Constant row sums factor out of a sum weighted by the second coordinate. -/
private theorem sum_pair_weights
    {α β : Type*} [Fintype α] [Fintype β]
    (f : β → α → Nat) (g : β → Nat) (row total : Nat)
    (hrow : ∀ b, (∑ a : α, f b a) = row)
    (hcol : (∑ b : β, g b) = total) :
    (∑ p : α × β, f p.2 p.1 * g p.2) = row * total := by
  classical
  rw [Fintype.sum_prod_type_right]
  have hinner (b : β) : (∑ a : α, f b a * g b) = row * g b := by
    rw [← Finset.sum_mul, hrow]
  simp_rw [hinner]
  rw [← Finset.mul_sum, hcol]

/-- The zero-left slice has total DDT mass `2^64` for every third key. -/
theorem zeroLeftSlice_total_mass (k₂ : V 32) :
    (∑ p : FeistelState, zeroLeftSlice k₂ p) = 2^64 := by
  classical
  have hcount : Fintype.card (V 32) = 2^32 := by
    rw [← FinEnum.card_eq_fintypeCard]
    exact FinEnum.card_bitVec 32
  have hsum :
      (∑ p : FeistelState,
        xorDDT_g (0#32) (1#32) (xor p.2 p.1) *
          xorDDT_g (0#32) p.2 (1#32)) = (2^32 : Nat) * 2^32 :=
    sum_pair_weights
      (fun bR aL : V 32 => xorDDT_g (0#32) (1#32) (xor bR aL))
      (fun bR : V 32 => xorDDT_g (0#32) bR (1#32)) (2^32) (2^32)
      (fun bR => (xorDDT_g_sum_output_xor (0#32) (1#32) bR).trans hcount)
      ((xorDDT_g_sum_input (0#32) (1#32)).trans hcount)
  calc
    (∑ p : FeistelState, zeroLeftSlice k₂ p) =
        ∑ p : FeistelState,
          xorDDT_g (0#32) (1#32) (xor p.2 p.1) *
            xorDDT_g (0#32) p.2 (1#32) := by
      apply Finset.sum_congr rfl
      intro p _
      exact xorDDT_rounds_three_zero_left_factorization
        (0#32) (0#32) k₂ p.1 (1#32) p.2
    _ = (2^32 : Nat) * 2^32 := hsum
    _ = 2^64 := by norm_num

/-! ### Saturation: finite mass already exhausted by a known subset -/

/-- If a finite set carries the entire mass of a natural-valued function,
    every point outside it has weight zero. -/
theorem zero_off_saturated_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (weight : α → Nat) (mass : Nat)
    (htotal : (∑ x : α, weight x) = mass)
    (hknown : (∑ x ∈ S, weight x) = mass)
    (x : α) (hx : x ∉ S) : weight x = 0 := by
  have hcompl : (∑ x ∈ Sᶜ, weight x) = 0 := by
    have hsplit := Finset.sum_add_sum_compl S weight
    rw [hknown, htotal] at hsplit
    omega
  exact (Finset.sum_eq_zero_iff.mp hcompl) x (Finset.mem_compl.mpr hx)

private def all64 : Finset FeistelState := predictedPairs.toFinset

/-- The 64 certified entries already consume the entire 2^64 mass. -/
theorem known64_total_mass (k₂ : V 32) :
    (∑ p ∈ all64, zeroLeftSlice k₂ p) = 2^64 := by
  have hcard : all64.card = 64 := by
    change predictedPairs.toFinset.card = 64
    rw [List.toFinset_card_of_nodup predictedPairs_nodup]
    exact predictedPairs_length
  calc
    (∑ p ∈ all64, zeroLeftSlice k₂ p) =
        ∑ _p ∈ all64, (2^58 : Nat) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact predictedPairs_exact_count k₂ p.1 p.2
        (by simpa only [all64, List.mem_toFinset] using hp)
    _ = all64.card * 2^58 := by simp
    _ = 2^64 := by rw [hcard]; norm_num

/-- Exact classification of the zero-left slice for every third round key. -/
theorem zeroLeftSlice_exact_iff_listed (k₂ aL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) =
      if (aL, bR) ∈ predictedPairs then 2^58 else 0 := by
  classical
  by_cases hmem : (aL, bR) ∈ predictedPairs
  · rewrite [ite_eq_left hmem]
    exact predictedPairs_exact_count k₂ aL bR hmem
  · rewrite [ite_eq_right hmem]
    change zeroLeftSlice k₂ (aL, bR) = 0
    apply zero_off_saturated_subset
      (S := all64) (weight := zeroLeftSlice k₂)
      (mass := 2^64)
      (zeroLeftSlice_total_mass k₂) (known64_total_mass k₂)
      (aL, bR)
    simpa only [all64, List.mem_toFinset] using hmem

/-- Positive DDT support is exactly the list of 64 certified pairs. -/
theorem zeroLeftSlice_possible_iff_listed (k₂ aL bR : V 32) :
    0 < xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      (aL, 1#32) (0#32, bR) ↔
      (aL, bR) ∈ predictedPairs := by
  rw [zeroLeftSlice_exact_iff_listed]
  by_cases h : (aL, bR) ∈ predictedPairs <;> norm_num [h]

end Magma.Evidence.ZeroLeft64Completeness
