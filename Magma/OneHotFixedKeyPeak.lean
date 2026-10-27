module

public import Magma.OneHotGlobalMaximum
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact fixed-key peaks and arithmetic counts of maximizing classes

For each 32-bit key, the one-bit-input, output-one DDT slice has exact peak
`512 * peakWeight q K`, with an explicit maximizing input bit. Here `q` is
key nibble five and `K` is the low twenty key bits. The unscaled peak is
`2^20 - K` at `q = 7`, `K` at `q = 8`, and `max (2^20 - K) K` at
`q = 12` or `13`; all other classes have peak `2^20`.

The full-word maximizer predicate is equivalent to the local class test.
Finite nibble counts and symbolic prefix counts give the arithmetic total
`2^8 * (15 + 12 * (2^20 - 1)) = 3221226240`, with complement `1073741056`.
The counting theorems concern this class-based expression; equality with
the cardinality of a filtered set of full words is not asserted here.
-/

open scoped BigOperators

namespace Magma.OneHotFixedKeyPeak

open Magma.CarryAutomaton
open Magma.OneHotExactCoefficientMasks
open Magma.OneHotKeyClasses
open Magma.OneHotFullKeyClassInvariant
open Magma.OneHotGlobalMaximum

private abbrev B : Nat :=
  2 ^ 20

/-! ### I. The exact peak of the four-bit S-box mask calculation. -/

/-- Unscaled count for an active one-hot input position. -/
def weight (q : Fin 16) (K : Nat) (r : Fin 4) : Nat :=
  (B - K) * coefficientBit q r +
    K * coefficientBit (nextNibble q) r

/-- A closed expression for the maximum over the four active input bits. -/
def peakWeight (q : Fin 16) (K : Nat) : Nat :=
  if q.val = 7 then B - K
  else if q.val = 8 then K
  else if q.val = 12 ∨ q.val = 13 then
    if 2 * K ≤ B then B - K else K
  else B

/-- An explicit maximizing input bit. On the two 'V-shaped' classes,
    its position switches as K passes B/2. -/
def peakBit (q : Fin 16) (K : Nat) : Fin 4 :=
  match q.val with
  | 0  => 3
  | 1  => 2
  | 2  => 1
  | 3  => 2
  | 4  => 3
  | 5  => 3
  | 6  => 1
  | 7  => 0
  | 8  => 0
  | 9  => 2
  | 10 => 1
  | 11 => 2
  | 12 => if 2 * K ≤ B then 2 else 0
  | 13 => if 2 * K ≤ B then 0 else 1
  | 14 => 1
  | _  => 3

/-- Every active position is bounded by the displayed peak.
    Only the 16 mask entries are inspected, never the word space. -/
theorem weight_le_peak (q : Fin 16) (K : Nat) (hK : K < B)
    (r : Fin 4) : weight q K r ≤ peakWeight q K := by
  change K < 1048576 at hK
  fin_cases q <;> fin_cases r <;>
    simp [weight, peakWeight, coefficientBit, coefficientMask,
      nextNibble, B] <;> (try split_ifs) <;> omega

/-- The selected bit reaches the upper bound exactly. -/
theorem peakBit_attains (q : Fin 16) (K : Nat) (hK : K < B) :
    weight q K (peakBit q K) = peakWeight q K := by
  change K < 1048576 at hK
  fin_cases q <;>
    simp [peakBit, weight, peakWeight, coefficientBit,
      coefficientMask, nextNibble, B] <;> (try split_ifs) <;> norm_num <;> omega

private theorem keyPrefix_lt (k : V 32) : k.toNat % B < B := by exact Nat.mod_lt _ (by norm_num [B])

/-- Upper bound at each one-hot input bit for a FIXED round key. -/
theorem fixed_key_peak_bound (k : V 32) (j : Fin 32) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤
      2 ^ 9 * peakWeight (keyNibble5 k) (k.toNat % B) := by
  by_cases hout : j.val < 20 ∨ 24 ≤ j.val
  · have hz := oneHot_outside_middle_zero k j hout
    change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 at hz
    simp [hz]
  · have hm : 20 ≤ j.val ∧ j.val < 24 := by omega
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j.val = 20 + r.val := by dsimp [r]; omega
    rw [hr, oneHot_g_DDT_exact_mask]
    exact Nat.mul_le_mul_left _
      (weight_le_peak (keyNibble5 k) (k.toNat % B) (keyPrefix_lt k) r)

/-- A concrete maximizing one-hot bit exists for EVERY 32-bit key.
    In particular this also covers the 256 keys with zero peak. -/
theorem fixed_key_peak_attained (k : V 32) :
    ∃ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) =
        2 ^ 9 * peakWeight (keyNibble5 k) (k.toNat % B) := by
  let r := peakBit (keyNibble5 k) (k.toNat % B)
  refine ⟨⟨20 + r.val, by omega⟩, ?_⟩
  rw [oneHot_g_DDT_exact_mask]
  exact congrArg (fun n : Nat => 2 ^ 9 * n)
    (peakBit_attains (keyNibble5 k) (k.toNat % B) (keyPrefix_lt k))

/-- Exact best differential count for a given key, with both the
    upper-bound and attainment parts (no `argmax` enumeration). -/
theorem fixed_key_peak_exact (k : V 32) :
    (∀ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤
        2 ^ 9 * peakWeight (keyNibble5 k) (k.toNat % B)) ∧
    (∃ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) =
        2 ^ 9 * peakWeight (keyNibble5 k) (k.toNat % B)) := by
  exact ⟨fixed_key_peak_bound k, fixed_key_peak_attained k⟩

/-! ### II. Only four exceptional nibble classes. -/

/-- At a fixed key, outside q=7,8,12,13 the full 2^29 maximum
    is attained independently of all other key bits. -/
theorem ordinary_class_peak (q : Fin 16) (K : Nat)
    (h7 : q.val ≠ 7) (h8 : q.val ≠ 8)
    (h12 : q.val ≠ 12) (h13 : q.val ≠ 13) :
    peakWeight q K = B := by
  simp [peakWeight, h7, h8, h12, h13]

/-- The four exceptional key nibble classes, all K in [0,B). -/
theorem exceptional_class_peak (q : Fin 16) (K : Nat) :
    (q.val = 7 → peakWeight q K = B - K) ∧
    (q.val = 8 → peakWeight q K = K) ∧
    (q.val = 12 ∨ q.val = 13 →
      peakWeight q K = if 2 * K ≤ B then B - K else K) := by
  constructor
  · intro h; simp [peakWeight, h]
  constructor
  · intro h; simp [peakWeight, h]
  · intro h
    rcases h with h | h <;>
      simp [peakWeight, h]

/-- The *actual* 32-bit DDT maximizer predicate is exactly the
    local sixteen-class predicate, with the two prefix regimes. -/
theorem real_key_attains_iff_class (k : V 32) :
    (∃ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 29) ↔
      if k.toNat % B = 0 then (keyNibble5 k).val ≠ 8
      else (keyNibble5 k).val ≠ 7 ∧
        (keyNibble5 k).val ≠ 8 ∧
        (keyNibble5 k).val ≠ 12 ∧
        (keyNibble5 k).val ≠ 13 := by
  rw [key_has_maximizing_bit_iff]
  by_cases hK : k.toNat % B = 0
  · simp [hK]
  · simp [hK]

/-! ### III. The exact arithmetic distribution of global maximizers. -/

/-- How many of the 16 possible key nibbles admit the global maximum
    if the lower 20 key bits vanish: exactly 15. -/
theorem zero_prefix_good_nibbles :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun q => q.val ≠ 8)).card = 15 := by decide

/-- If the lower prefix is nonzero, exactly 12 of 16 nibble classes
    attain the global maximum. -/
theorem nonzero_prefix_good_nibbles :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun q => q.val ≠ 7 ∧ q.val ≠ 8 ∧
        q.val ≠ 12 ∧ q.val ≠ 13)).card = 12 := by decide

/-- Exact number of available nonzero 20-bit prefixes. -/
theorem nonzero_prefix_count :
    ((Finset.univ : Finset (Fin B)).filter
      (fun K => K ≠ 0)).card = B - 1 := by
  have hzero : ((0 : Fin B) ∈ (Finset.univ : Finset (Fin B))) := by simp
  rw [Finset.filter_ne', Finset.card_erase_of_mem hzero]
  simp [B]

/-- There are 256 independent choices of the upper eight key bits.
    The other 24 bits are exactly (q,K). -/
def countedMaximizingKeys : Nat :=
  2 ^ 8 * (15 + 12 * (B - 1))

/-- Evaluation of the class-based arithmetic count. This theorem does not
    itself identify that expression with a filtered full-word cardinality. -/
theorem countedMaximizingKeys_exact :
    countedMaximizingKeys = 3221226240 := by
  norm_num [countedMaximizingKeys, B]

/-- Number of key values not attaining the global one-hot maximum. -/
theorem countedNonMaximizingKeys_exact :
    2 ^ 32 - countedMaximizingKeys = 1073741056 := by
  norm_num [countedMaximizingKeys, B]

/-- Numerically, the maximum-attaining fraction differs from 3/4 by
    exactly 3 / 2^24. An integer identity avoids floating-point math. -/
theorem key_count_three_quarters_correction :
    countedMaximizingKeys = 3 * 2 ^ 30 + 3 * 2 ^ 8 := by
  norm_num [countedMaximizingKeys, B]

end Magma.OneHotFixedKeyPeak
