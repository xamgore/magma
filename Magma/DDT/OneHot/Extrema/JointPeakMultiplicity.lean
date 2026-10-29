module

public import Magma.DDT.OneHot.Extrema.MaximizingBitMultiplicity
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Joint fibers of one-bit DDT peaks and maximizing-position counts

For each actual 32-bit round key, the joint cell records its one-bit DDT
peak `2^9 * t` and the number `n` of input positions attaining that peak.
Its cardinality is exactly 256 times the corresponding local `(q, K)`
fiber, where `q` is key nibble five and `K` is the low twenty key bits.

The zero-peak cell with all 32 positions tied and the global-peak cell
with four positions tied each contain exactly 256 keys. The interior
joint fibers are reduced symbolically, without evaluating their counts.
-/

open scoped BigOperators

namespace Magma.OneHotJointPeakMultiplicity

open Magma.CarryAutomaton
open Magma.OneHotFixedKeyPeak
open Magma.OneHotCompletePeakHistogram
open Magma.OneHotMaximizingBitMultiplicity
open Magma.OneHotKeyClasses

private abbrev B : Nat :=
  2 ^ 20

private abbrev Parts :=
  Fin 256 × (Fin 16 × Fin B)

/-- Actual round keys whose best one-hot DDT is `2^9*t` and whose
    best DDT is attained at exactly `n` of the 32 input positions.
    In particular, if the peak is zero, all 32 positions tie. -/
def keysAtPeakWithTies (t n : Nat) : Finset (V 32) :=
  keysAtWeight t ∩ keysWithTies n

/-- The small-dimensional fiber of the SAME joint characteristic. -/
def peakTiePairs (t n : Nat) : Finset (Fin 16 × Fin B) :=
  Finset.univ.filter (fun p =>
    peakWeight p.1 p.2.val = t ∧
      tieMultiplicity p.1 p.2.val = n)

/-- The joint event refers to the actual one-round DDT of Magma,
    not to an unverified approximation. -/
theorem mem_keysAtPeakWithTies_iff_real_ddt
    (k : (V 32)) (t n : Nat) :
    k ∈ keysAtPeakWithTies t n ↔
      (∀ j : Fin 32,
        xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤ 2 ^ 9 * t) ∧
      (∃ j : Fin 32,
        xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 9 * t) ∧
      (actualMaximizers k).card = n := by
  simp only [keysAtPeakWithTies, Finset.mem_inter]
  rw [mem_keysAtWeight_iff_true_peak]
  simp only [keysWithTies, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_assoc

/-! ### The exact 32-bit-key to (q,K) cardinality bridge. -/

private def keyPartsEquiv : Parts ≃ (V 32) := by
  let e₁ : Parts ≃ Fin (256 * (16 * B)) :=
    (Equiv.prodCongr (Equiv.refl (Fin 256)) (finProdFinEquiv : Fin 16 × Fin B ≃ Fin (16 * B))).trans
      (finProdFinEquiv : Fin 256 × Fin (16 * B) ≃ Fin (256 * (16 * B)))
  have hsize : 256 * (16 * B) = 2 ^ 32 := by norm_num [B]
  let e₂ : Fin (256 * (16 * B)) ≃ (V 32) :=
    (finCongr hsize).trans (BitVec.equivFin (m := 32)).toEquiv.symm
  exact e₁.trans e₂

private theorem keyParts_toNat (p : Parts) :
    (keyPartsEquiv p).toNat = p.2.2.val + B * p.2.1.val + (16 * B) * p.1.val := by rfl

private theorem keyParts_class (p : Parts) :
    (keyPartsEquiv p).toNat % B = p.2.2.val ∧ (keyNibble5 (keyPartsEquiv p)).val = p.2.1.val := by
  have hv := keyParts_toNat p
  have hq := p.2.1.isLt
  have hl := p.2.2.isLt
  norm_num [B] at hv hl
  constructor
  · change (keyPartsEquiv p).toNat % 1048576 = p.2.2.val
    omega
  · change ((keyPartsEquiv p).toNat / 1048576) % 16 = p.2.1.val
    omega

/-- For EVERY `t,n` (including the endpoints), the number of REAL
    32-bit Magma keys with the joint property is exactly 256 times
    the cardinality of its local (q,K) fiber. No full-key search. -/
theorem joint_keys_card_eq_local_fiber (t n : Nat) :
    (keysAtPeakWithTies t n).card = 256 * (peakTiePairs t n).card := by
  have hmem (p : Parts) :
      p ∈ ((Finset.univ : Finset Parts).filter
        (fun p => peakWeight p.2.1 p.2.2.val = t ∧
          tieMultiplicity p.2.1 p.2.2.val = n)) ↔
      keyPartsEquiv p ∈ keysAtPeakWithTies t n := by
    have hk := keyParts_class p
    have hq : keyNibble5 (keyPartsEquiv p) = p.2.1 := Fin.ext hk.2
    simp only [keysAtPeakWithTies, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and,
      keysAtWeight, keysWithTies]
    rw [actualMaximizers_card, hq, hk.1]
  have hcard := Finset.card_equiv keyPartsEquiv hmem
  have hfiber :
      ((Finset.univ : Finset Parts).filter
        (fun p => peakWeight p.2.1 p.2.2.val = t ∧
          tieMultiplicity p.2.1 p.2.2.val = n)) =
        (Finset.univ : Finset (Fin 256)) ×ˢ peakTiePairs t n := by
    ext p
    simp [peakTiePairs]
  rw [← hcard, hfiber, Finset.card_product]
  simp

/-- Any nonempty joint cell refines the already proved histogram
    of maximal DDT values. -/
theorem joint_card_le_peak_card (t n : Nat) :
    (keysAtPeakWithTies t n).card ≤ (keysAtWeight t).card := by
  exact Finset.card_le_card Finset.inter_subset_left

/-- And it refines the already proved histogram of argmax counts. -/
theorem joint_card_le_ties_card (t n : Nat) :
    (keysAtPeakWithTies t n).card ≤ (keysWithTies n).card := by
  exact Finset.card_le_card Finset.inter_subset_right

/-! ### Two exact extreme cells, without any arithmetic enumeration. -/

/-- When the best DDT is zero, all 32 positions attain the zero peak. -/
private theorem zero_peak_has_all_ties (k : (V 32))
    (hk : k ∈ keysAtWeight 0) : k ∈ keysWithTies 32 := by
  have hpeak : peakWeight (keyNibble5 k) (k.toNat % B) = 0 :=
    (Finset.mem_filter.mp hk).2
  have ht : (actualMaximizers k).card = 32 := by
    rw [actualMaximizers_card]
    simp [tieMultiplicity, hpeak]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, ht⟩

/-- The zero-peak, 32-way-tie joint fiber consists of exactly 256 keys. -/
theorem zero_peak_all_32_ties :
    (keysAtPeakWithTies 0 32).card = 256 := by
  have heq : keysAtPeakWithTies 0 32 = keysAtWeight 0 := by
    ext k
    constructor
    · intro hk
      exact (Finset.mem_inter.mp hk).1
    · intro hk
      exact Finset.mem_inter.mpr ⟨hk, zero_peak_has_all_ties k hk⟩
  rw [heq]
  exact zero_endpoint

/-- A four-way argmax can occur only at the global peak, never at an
    intermediate value. The proof uses the previous three-regime
    reduction and ONLY the sixteen possible S-box masks. -/
private theorem four_ties_force_top (q : Fin 16) (K : Nat)
    (hK : K < B) (hfour : tieMultiplicity q K = 4) :
    peakWeight q K = B := by
  by_cases hz : K = 0
  · subst K
    have hsmall (q : Fin 16) :
        tieMultiplicity q 0 = 4 → peakWeight q 0 = B := by
      fin_cases q <;> decide
    exact hsmall q hfour
  · have hreg := tieMultiplicity_regimes q K hK
    rw [hreg, ite_eq_right hz] at hfour
    by_cases hm : 2 * K = B
    · simp only [ite_eq_left hm] at hfour
      have hnot (q : Fin 16) :
          tieMultiplicity q (B / 2) ≠ 4 := by
        fin_cases q <;> decide
      exact False.elim (hnot q hfour)
    · simp only [ite_eq_right hm] at hfour
      have hnot (q : Fin 16) :
          tieMultiplicity q 1 ≠ 4 := by
        fin_cases q <;> decide
      exact False.elim (hnot q hfour)

/-- All 256 keys with four maximizing bits have peak exactly 2^29. -/
theorem global_peak_four_ties :
    (keysAtPeakWithTies B 4).card = 256 := by
  have heq : keysAtPeakWithTies B 4 = keysWithTies 4 := by
    ext k
    constructor
    · intro hk
      exact (Finset.mem_inter.mp hk).2
    · intro hk
      have ht : (actualMaximizers k).card = 4 :=
        (Finset.mem_filter.mp hk).2
      rw [actualMaximizers_card] at ht
      have hK : k.toNat % B < B :=
        Nat.mod_lt _ (by norm_num [B])
      have hpeak := four_ties_force_top (keyNibble5 k) (k.toNat % B) hK ht
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ k, hpeak⟩, hk⟩
  rw [heq]
  exact actual_key_four_maximizing_bits

/-- Sanity checks: these are two distinct classes, each with 256 keys. -/
theorem two_extreme_joint_cells_total :
    (keysAtPeakWithTies 0 32).card +
      (keysAtPeakWithTies B 4).card = 512 := by
  rw [zero_peak_all_32_ties, global_peak_four_ties]

end Magma.OneHotJointPeakMultiplicity
