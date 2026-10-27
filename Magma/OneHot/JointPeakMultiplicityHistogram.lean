module

public import Magma.OneHot.JointPeakMultiplicity
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Complete joint histogram of one-bit DDT peaks and maximizing positions

Each cell counts actual 32-bit keys with peak `512 * t` and exactly `n`
maximizing input positions. The local fiber reduction is evaluated
symbolically in the zero, lower, midpoint, upper, and global-peak regimes.
Only finite nibble classes are enumerated; the twenty-bit prefix counts
are obtained from explicit singleton, pair, and product cardinalities.

Nonzero intermediate peaks have at most two maximizing positions. The
nonzero cells in the histogram account for all `2^32` round keys.
-/

open scoped BigOperators

namespace Magma.OneHotJointPeakMultiplicityHistogram

open Magma.OneHotJointPeakMultiplicity
open Magma.OneHotFixedKeyPeak
open Magma.OneHotMaximizingBitMultiplicity
open Magma.OneHotKeyClasses

private abbrev B : Nat :=
  2 ^ 20

private abbrev H : Nat :=
  2 ^ 19

private theorem peakWeight_formula (q : Fin 16) (K : Nat) :
    peakWeight q K =
      if q.val = 7 then B - K
      else
        if q.val = 8 then K
        else if q.val = 12 ∨ q.val = 13 then if 2 * K ≤ B then B - K else K else B := by
  rfl

private def near (t : Nat) (ht : t < B) : Fin B :=
  ⟨t, ht⟩

private def far (t : Nat) (h0 : 0 < t) (ht : t < B) : Fin B :=
  ⟨B - t, by omega⟩

private def vCandidates (t : Nat) (h0 : 0 < t) (ht : t < B) : Finset (Fin B) :=
  if B ≤ 2 * t then {near t ht, far t h0 ht} else ∅

private theorem vCandidates_card (t : Nat) (h0 : 0 < t) (ht : t < B) :
    (vCandidates t h0 ht).card = if 2 * t < B then 0 else if 2 * t = B then 1 else 2 := by
  by_cases hlt : 2 * t < B
  · have hn : ¬B ≤ 2 * t := by omega
    simp [vCandidates, hlt, hn]
  · have hle : B ≤ 2 * t := by omega
    by_cases heq : 2 * t = B
    · have hsame : near t ht = far t h0 ht := by
        apply Fin.ext
        simp only [near, far]
        omega
      simp [vCandidates, heq, hsame]
    · have hdiff : near t ht ≠ far t h0 ht := by
        intro h
        have hv := congrArg Fin.val h
        simp only [near, far] at hv
        omega
      simp [vCandidates, hle, hlt, heq, Finset.card_pair hdiff]

private theorem vCandidates_mem_iff (t : Nat) (h0 : 0 < t) (ht : t < B) (K : Fin B) :
    K ∈ vCandidates t h0 ht ↔ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t) := by
  by_cases h : B ≤ 2 * t
  · simp [vCandidates, h, near, far, Fin.ext_iff]
  · simp [vCandidates, h]

/-! ## I. Middle-range fibers: two linear classes and two V-classes. -/

private theorem middle_peak_iff (t : Nat) (h0 : 0 < t) (ht : t < B) (q : Fin 16) (K : Fin B) :
    peakWeight q K.val = t ↔
      (q.val = 7 ∧ K.val = B - t) ∨
        (q.val = 8 ∧ K.val = t) ∨
        ((q.val = 12 ∨ q.val = 13) ∧ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t)) := by
  have hK := K.isLt
  norm_num [B] at ht hK
  fin_cases q <;> simp [peakWeight_formula, B] <;> (try split_ifs) <;> omega

/-- Local tie cardinalities for the only four classes that can give
    an intermediate nonzero peak. No prefix-space evaluation. -/
private theorem special_middle_ties (q : Fin 16) (K : Nat)
    (hK : K < B) (hz : K ≠ 0)
    (hq : q.val = 7 ∨ q.val = 8 ∨ q.val = 12 ∨ q.val = 13) :
    tieMultiplicity q K =
      if q.val = 7 ∨ q.val = 8 then 2
      else if 2 * K = B then 2 else 1 := by
  rw [tieMultiplicity_regimes q K hK]
  simp only [ite_eq_right hz]
  by_cases hm : 2 * K = B
  · rw [ite_eq_left hm]
    fin_cases q <;> simp_all [B] <;> decide
  · rw [ite_eq_right hm]
    fin_cases q <;> simp_all [B] <;> decide

private theorem middle_tie_iff (t : Nat) (h0 : 0 < t) (ht : t < B) (q : Fin 16) (K : Fin B)
    (hp : peakWeight q K.val = t) :
    tieMultiplicity q K.val = if q.val = 7 ∨ q.val = 8 then 2 else if 2 * t = B then 2 else 1 := by
  have hc := (middle_peak_iff t h0 ht q K).mp hp
  have hK := K.isLt
  have hz : K.val ≠ 0 := by
    rcases hc with h | h | h
    · omega
    · omega
    · rcases h with ⟨_, _, h⟩
      rcases h with h | h <;> omega
  have hq : q.val = 7 ∨ q.val = 8 ∨ q.val = 12 ∨ q.val = 13 := by
    rcases hc with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  rw [special_middle_ties q K.val hK hz hq]
  by_cases hlinear : q.val = 7 ∨ q.val = 8
  · simp [hlinear]
  · have hv : K.val = t ∨ K.val = B - t := by
      rcases hc with h | h | h
      · exact False.elim (hlinear (Or.inl h.1))
      · exact False.elim (hlinear (Or.inr h.1))
      · exact h.2.2
    have hm : (2 * K.val = B) ↔ (2 * t = B) := by rcases hv with hv | hv <;> omega
    simp [hlinear, hm]

private def linearPair (t : Nat) (h0 : 0 < t) (ht : t < B) : Finset (Fin 16 × Fin B) :=
  (({(7 : Fin 16)} : Finset (Fin 16)) ×ˢ {far t h0 ht}) ∪
    (({(8 : Fin 16)} : Finset (Fin 16)) ×ˢ {near t ht})

private def veePairs (t : Nat) (h0 : 0 < t) (ht : t < B) : Finset (Fin 16 × Fin B) :=
  ({(12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16)) ×ˢ vCandidates t h0 ht

private theorem middle_models_disjoint (t : Nat) (h0 : 0 < t) (ht : t < B) :
    Disjoint (linearPair t h0 ht) (veePairs t h0 ht) := by
  apply Finset.disjoint_left.mpr
  intro p hp hv
  have hqv : p.1 = (12 : Fin 16) ∨ p.1 = (13 : Fin 16) := by
    have h := (Finset.mem_product.mp hv).1
    simpa using h
  have hql : p.1 = (7 : Fin 16) ∨ p.1 = (8 : Fin 16) := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Or.inl (by simpa using (Finset.mem_product.mp hp).1)
    · exact Or.inr (by simpa using (Finset.mem_product.mp hp).1)
  rcases hql with hql | hql <;> rcases hqv with hqv | hqv <;> simp_all

private theorem middle_models_card (t : Nat) (h0 : 0 < t) (ht : t < B) :
    (linearPair t h0 ht).card = 2 ∧ (veePairs t h0 ht).card = 2 * (vCandidates t h0 ht).card := by
  constructor
  · have hd :
      Disjoint (({(7 : Fin 16)} : Finset (Fin 16)) ×ˢ {far t h0 ht})
        (({(8 : Fin 16)} : Finset (Fin 16)) ×ˢ {near t ht}) := by
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      have h7 := (Finset.mem_product.mp hp).1
      have h8 := (Finset.mem_product.mp hp').1
      simp at h7 h8
      exact absurd (h7.symm.trans h8) (by decide)
    rw [linearPair, Finset.card_union_of_disjoint hd]
    simp
  · simp [veePairs, Finset.card_product]

private theorem middle_fiber_eq (t n : Nat) (h0 : 0 < t) (ht : t < B) :
    peakTiePairs t n =
      (if n = 2 then linearPair t h0 ht else ∅) ∪
        (if n = (if 2 * t = B then 2 else 1) then veePairs t h0 ht else ∅) := by
  ext p
  rcases p with ⟨q, K⟩
  have hp := middle_peak_iff t h0 ht q K
  simp only [peakTiePairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  have hl :
    (q, K) ∈ linearPair t h0 ht ↔ (q.val = 7 ∧ K.val = B - t) ∨ (q.val = 8 ∧ K.val = t) := by
    simp [linearPair, Fin.ext_iff, near, far]
  have hv :
    (q, K) ∈ veePairs t h0 ht ↔
      (q.val = 12 ∨ q.val = 13) ∧ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t) := by
    simp only [veePairs, Finset.mem_product]
    rw [vCandidates_mem_iff t h0 ht K]
    simp [Fin.ext_iff, and_comm]
  have mem_if (c : Prop) [Decidable c] (s : Finset (Fin 16 × Fin B)) :
    (q, K) ∈ (if c then s else ∅) ↔ c ∧ (q, K) ∈ s := by split_ifs <;> simp_all
  by_cases hpeak : peakWeight q K.val = t
  · have htie := middle_tie_iff t h0 ht q K hpeak
    simp only [hpeak, true_and]
    rw [hp] at hpeak
    rw [mem_if, mem_if, hl, hv]
    rcases hpeak with hlin | hlin | hvee
    · simp [hlin] at htie ⊢
      omega
    · simp [hlin] at htie ⊢
      omega
    · have hq : ¬(q.val = 7 ∨ q.val = 8) := by omega
      simp [hvee, hq] at htie ⊢
      omega
  · have hnot :
      ¬((q.val = 7 ∧ K.val = B - t) ∨
          (q.val = 8 ∧ K.val = t) ∨
          ((q.val = 12 ∨ q.val = 13) ∧ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t))) := by
      exact fun hh => hpeak (hp.mpr hh)
    have hnlin : ¬((q.val = 7 ∧ K.val = B - t) ∨ (q.val = 8 ∧ K.val = t)) := by
      intro h
      exact hnot (h.elim Or.inl (Or.inr ∘ Or.inl))
    have hnvee : ¬((q.val = 12 ∨ q.val = 13) ∧ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t)) := by
      intro h
      exact hnot (Or.inr (Or.inr h))
    rw [mem_if, mem_if, hl, hv]
    simp [hpeak, hnlin, hnvee]

private theorem middle_fiber_card (t n : Nat) (h0 : 0 < t) (ht : t < B) :
    (peakTiePairs t n).card =
      (if n = 2 then 2 else 0) +
        (if n = (if 2 * t = B then 2 else 1) then
          2 * (if 2 * t < B then 0 else if 2 * t = B then 1 else 2)
        else 0) := by
  rw [middle_fiber_eq t n h0 ht]
  have hd := middle_models_disjoint t h0 ht
  have hcard := middle_models_card t h0 ht
  have hv := vCandidates_card t h0 ht
  by_cases h2 : n = 2
  · by_cases hvn : n = (if 2 * t = B then 2 else 1)
    · simp only [ite_eq_left h2, ite_eq_left hvn]
      rw [Finset.card_union_of_disjoint hd, hcard.1, hcard.2, hv]
    · simp only [ite_eq_left h2, ite_eq_right hvn, Finset.union_empty, hcard.1, Nat.add_zero]
  · by_cases hvn : n = (if 2 * t = B then 2 else 1)
    · simp only [ite_eq_right h2, ite_eq_left hvn, Finset.empty_union, hcard.2, hv, Nat.zero_add]
    · simp only [ite_eq_right h2, ite_eq_right hvn, Finset.union_empty, Finset.card_empty,
        Nat.zero_add]

/-! ## II. Top-peak fiber: twelve unrestricted classes plus three
    classes present only at zero prefix. -/

private def regularQ : Finset (Fin 16) :=
  Finset.univ.filter (fun q => q.val ≠ 7 ∧ q.val ≠ 8 ∧ q.val ≠ 12 ∧ q.val ≠ 13)

private def topZeroQ (n : Nat) : Finset (Fin 16) :=
  (regularQ ∪ ({(7 : Fin 16), (12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16))).filter
    (fun q => tieMultiplicity q 0 = n)

private def topPositiveQ (n : Nat) : Finset (Fin 16) :=
  regularQ.filter (fun q => tieMultiplicity q 1 = n)

private theorem top_peak_iff (q : Fin 16) (K : Fin B) :
    peakWeight q K.val = B ↔
      q ∈ regularQ ∨ ((q.val = 7 ∨ q.val = 12 ∨ q.val = 13) ∧ K.val = 0) := by
  have hk := K.isLt
  norm_num [B] at hk
  fin_cases q <;> simp [peakWeight_formula, regularQ, B] <;> (try split_ifs) <;> omega

private theorem top_regular_ties (q : Fin 16) (K : Fin B) (hq : q ∈ regularQ) (hz : K.val ≠ 0) :
    tieMultiplicity q K.val = tieMultiplicity q 1 := by
  rw [tieMultiplicity_regimes q K.val K.isLt]
  simp only [ite_eq_right hz]
  by_cases hm : 2 * K.val = B
  · rw [ite_eq_left hm]
    have hsmall (q : Fin 16) (hq : q ∈ regularQ) :
      tieMultiplicity q (B / 2) = tieMultiplicity q 1 := by
      fin_cases q <;> simp_all [regularQ] <;> decide
    exact hsmall q hq
  · simp [hm]

private theorem top_fiber_eq (n : Nat) :
    peakTiePairs B n =
      (topZeroQ n ×ˢ {(0 : Fin B)}) ∪
        (topPositiveQ n ×ˢ ((Finset.univ : Finset (Fin B)).erase 0)) := by
  ext p
  rcases p with ⟨q, K⟩
  by_cases hz : K = (0 : Fin B)
  · subst K
    have hallowed :
      peakWeight q 0 = B ↔
        q ∈ regularQ ∪ ({(7 : Fin 16), (12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16)) := by
      fin_cases q <;> decide
    simp [peakTiePairs, topZeroQ, topPositiveQ, hallowed]
  · have hzval : K.val ≠ 0 := by
      intro h
      exact hz (Fin.ext h)
    have ht : peakWeight q K.val = B ↔ q ∈ regularQ := by
      rw [top_peak_iff]
      simp [hzval]
    simp only [peakTiePairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product]
    by_cases hr : q ∈ regularQ
    · have htie := top_regular_ties q K hr hzval
      simp [topZeroQ, topPositiveQ, ht, hr, hz, htie]
    · simp [topZeroQ, topPositiveQ, ht, hr, hz]

private theorem top_fiber_card (n : Nat) :
    (peakTiePairs B n).card = (topZeroQ n).card + (B - 1) * (topPositiveQ n).card := by
  rw [top_fiber_eq]
  have hd :
    Disjoint (topZeroQ n ×ˢ {(0 : Fin B)})
      (topPositiveQ n ×ˢ ((Finset.univ : Finset (Fin B)).erase 0)) := by
    apply Finset.disjoint_left.mpr
    intro p ha hb
    have hz : p.2 = (0 : Fin B) := by simpa using (Finset.mem_product.mp ha).2
    have hn : p.2 ≠ (0 : Fin B) := by simpa using (Finset.mem_product.mp hb).2
    exact hn hz
  rw [Finset.card_union_of_disjoint hd]
  have herase : ((Finset.univ : Finset (Fin B)).erase 0).card = B - 1 := by
    rw [Finset.card_erase_of_mem (by simp : (0 : Fin B) ∈ (Finset.univ : Finset (Fin B)))]
    simp
  simp [Finset.card_product, herase, Nat.mul_comm]

private theorem top_small_counts :
    (topZeroQ 1).card = 4 ∧
      (topPositiveQ 1).card = 8 ∧
      (topZeroQ 2).card = 6 ∧
      (topPositiveQ 2).card = 3 ∧
      (topZeroQ 3).card = 4 ∧
      (topPositiveQ 3).card = 1 ∧ (topZeroQ 4).card = 1 ∧ (topPositiveQ 4).card = 0 := by
  decide

private theorem top_small_only (n : Nat) :
    n ∉ ({1, 2, 3, 4} : Finset Nat) → (topZeroQ n).card = 0 ∧ (topPositiveQ n).card = 0 := by
  intro hn
  constructor
  · apply Finset.card_eq_zero.mpr
    simp only [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    have hsmall (q : Fin 16)
      (hq : q ∈ regularQ ∪ ({(7 : Fin 16), (12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16))) :
      tieMultiplicity q 0 ∈ ({1, 2, 3, 4} : Finset Nat) := by
      fin_cases q <;> simp_all [regularQ] <;> decide
    have hv := hsmall q (Finset.mem_filter.mp hq).1
    exact hn ((Finset.mem_filter.mp hq).2 ▸ hv)
  · apply Finset.card_eq_zero.mpr
    simp only [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    have hsmall (q : Fin 16) (hq : q ∈ regularQ) :
      tieMultiplicity q 1 ∈ ({1, 2, 3, 4} : Finset Nat) := by
      fin_cases q <;> simp_all [regularQ] <;> decide
    have hv := hsmall q (Finset.mem_filter.mp hq).1
    exact hn ((Finset.mem_filter.mp hq).2 ▸ hv)

/-! ## III. All actual 32-bit key cardinalities. -/

/-- Every joint cell of the TRUE DDT peak and its argmax count. -/
theorem actual_joint_peak_histogram (t n : Nat) (ht : t ≤ B) :
    (keysAtPeakWithTies t n).card =
      if t = 0 then (if n = 32 then 256 else 0)
      else if 2 * t < B then (if n = 2 then 512 else 0)
      else if 2 * t = B then (if n = 2 then 1024 else 0)
      else if t < B then
        (if n = 1 then 1024 else if n = 2 then 512 else 0)
      else if n = 1 then 2147482624
      else if n = 2 then 805307136
      else if n = 3 then 268436224
      else if n = 4 then 256 else 0 := by
  rw [joint_keys_card_eq_local_fiber]
  by_cases hz : t = 0
  · subst t
    by_cases hn : n = 32
    · subst n
      have h := zero_peak_all_32_ties
      rw [joint_keys_card_eq_local_fiber] at h
      norm_num at h ⊢
      exact h
    · have he : peakTiePairs 0 n = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hpeak : peakWeight p.1 p.2.val = 0 :=
          (Finset.mem_filter.mp hp).2.1
        have hcount : tieMultiplicity p.1 p.2.val = n :=
          (Finset.mem_filter.mp hp).2.2
        have hzero (q : Fin 16) (K : Fin B)
            (h : peakWeight q K.val = 0) :
            tieMultiplicity q K.val = 32 := by
          simp only [tieMultiplicity, ite_eq_left h]
        exact hn (hcount.symm.trans (hzero p.1 p.2 hpeak))
      simp [he, hn]
  by_cases htop : t = B
  · subst t
    rw [top_fiber_card]
    rcases top_small_counts with ⟨h11,h12,h21,h22,h31,h32,h41,h42⟩
    by_cases h1 : n = 1
    · subst n; rw [h11,h12]; norm_num [B]
    by_cases h2 : n = 2
    · subst n; rw [h21,h22]; norm_num [B]
    by_cases h3 : n = 3
    · subst n; rw [h31,h32]; norm_num [B]
    by_cases h4 : n = 4
    · subst n; rw [h41,h42]; norm_num [B]
    have hzero := top_small_only n (by simp [h1,h2,h3,h4])
    rw [hzero.1, hzero.2]
    simp [h1,h2,h3,h4, B]
  have h0 : 0 < t := by omega
  have hB : t < B := by omega
  rw [middle_fiber_card t n h0 hB]
  by_cases hlt : 2 * t < B
  · simp [hz, hlt]
  by_cases hmid : 2 * t = B
  · simp [hz, hmid]; split_ifs <;> omega
  · simp [hz, hlt, hmid, hB]; split_ifs <;> omega

/-- Nonzero intermediate peaks cannot have three or more maximizing bits. -/
theorem intermediate_peak_at_most_two_ties
    (t n : Nat) (ht : 0 < t) (hu : t < B) (hn : 2 < n) :
    (keysAtPeakWithTies t n).card = 0 := by
  rw [actual_joint_peak_histogram t n (by omega)]
  split_ifs <;> omega

/-- The extrema from the preceding module are recovered. -/
theorem joint_two_extremes :
    (keysAtPeakWithTies 0 32).card = 256 ∧
      (keysAtPeakWithTies B 4).card = 256 := by
  constructor
  · simpa [B] using actual_joint_peak_histogram 0 32 (by omega : 0 ≤ B)
  · simpa [B] using actual_joint_peak_histogram B 4 (le_refl B)

/-- Total mass of all displayed nonzero cells equals the key space. -/
theorem joint_distribution_total :
    256 + 512 * (2 ^ 19 - 1) + 1024 +
      (1024 + 512) * (2 ^ 19 - 1) +
      2147482624 + 805307136 + 268436224 + 256 = 2 ^ 32 := by
  norm_num

end Magma.OneHotJointPeakMultiplicityHistogram
