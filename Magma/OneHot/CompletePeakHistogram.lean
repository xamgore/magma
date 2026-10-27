module

public import Magma.OneHot.ActualKeyCardinality
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Complete histogram of fixed-key one-bit DDT peaks

`keysAtWeight t` consists of the actual 32-bit round keys whose largest
one-bit-input, output-one DDT count is `512 * t`. A key-coordinate bijection
reduces each fiber cardinality to a symbolic count over the key nibble and
low twenty bits, with 256 independent choices of the high eight bits.

For `0 ≤ t ≤ 2^20`, the distribution is:

| Weight `t` | Keys at each weight |
| --- | --- |
| `0` | `256` |
| `0 < t < 2^19` | `512` |
| `2^19` | `1024` |
| `2^19 < t < 2^20` | `1536` |
| `2^20` | `3221226240` |

The two V-shaped nibble classes contribute two low-prefix choices away
from their midpoint and one at the midpoint. Both endpoints are counted
separately. The resulting five frequency groups sum to `2^32`; no full-word
or twenty-bit-prefix enumeration is used.
-/

open scoped BigOperators

namespace Magma.OneHotCompletePeakHistogram

open Magma.CarryAutomaton
open Magma.OneHotFixedKeyPeak
open Magma.OneHotKeyClasses

private abbrev B : Nat :=
  2 ^ 20

private abbrev Parts :=
  Fin 256 × (Fin 16 × Fin B)

private theorem peakWeight_formula (q : Fin 16) (K : Nat) :
    peakWeight q K =
      if q.val = 7 then B - K
      else
        if q.val = 8 then K
        else if q.val = 12 ∨ q.val = 13 then if 2 * K ≤ B then B - K else K else B := by
  rfl

/-! ## 1. The exact peak is a fiber of the (q,K) function. -/

/-- Actual 32-bit keys whose *true* largest one-hot DDT equals `512*t`.
    The fixed-key maximum theorem identifies this value without a max
    over a gigantic table. -/
def keysAtWeight (t : Nat) : Finset (V 32) :=
  Finset.univ.filter (fun k =>
    peakWeight (keyNibble5 k) (k.toNat % B) = t)

/-- Membership describes the genuine best one-hot DDT, not merely
    an arithmetic approximation. This is a direct consequence of the
    previously kernel-proved fixed-key upper bound and its witness. -/
theorem mem_keysAtWeight_iff_true_peak (k : (V 32)) (t : Nat) :
    k ∈ keysAtWeight t ↔
      (∀ j : Fin 32,
        xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ≤ 2 ^ 9 * t) ∧
      (∃ j : Fin 32,
        xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 9 * t) := by
  constructor
  · intro hk
    have hw : peakWeight (keyNibble5 k) (k.toNat % B) = t :=
      (Finset.mem_filter.mp hk).2
    constructor
    · intro j
      simpa [hw] using (fixed_key_peak_exact k).1 j
    · obtain ⟨j, hj⟩ := (fixed_key_peak_exact k).2
      exact ⟨j, by simpa [hw] using hj⟩
  · rintro ⟨hb, ⟨j, hj⟩⟩
    obtain ⟨jmax, hm⟩ := (fixed_key_peak_exact k).2
    have hle := (fixed_key_peak_exact k).1 j
    have hge := hb jmax
    have hw : peakWeight (keyNibble5 k) (k.toNat % B) = t := by
      norm_num at hj hle hm hge
      change peakWeight (keyNibble5 k) (k.toNat % 1048576) = t
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hw⟩

/-- Keys divided into their (q,K) coordinates. The cardinality is a
    symbolic finite set; it is never evaluated over its million elements. -/
private def pairFiber (t : Nat) : Finset (Fin 16 × Fin B) :=
  Finset.univ.filter (fun p => peakWeight p.1 p.2.val = t)

/-- Exactly the same decomposition used in the proved cardinality theorem. -/
private def keyPartsEquiv : Parts ≃ (V 32) := by
  let e₁ : Parts ≃ Fin (256 * (16 * B)) :=
    (Equiv.prodCongr (Equiv.refl (Fin 256))
      (finProdFinEquiv : Fin 16 × Fin B ≃ Fin (16 * B))).trans
      (finProdFinEquiv : Fin 256 × Fin (16 * B) ≃ Fin (256 * (16 * B)))
  have hsize : 256 * (16 * B) = 2 ^ 32 := by norm_num [B]
  let e₂ : Fin (256 * (16 * B)) ≃ (V 32) :=
    (finCongr hsize).trans (BitVec.equivFin (m := 32)).toEquiv.symm
  exact e₁.trans e₂

private theorem keyParts_toNat (p : Parts) :
    (keyPartsEquiv p).toNat = p.2.2.val + B * p.2.1.val + (16 * B) * p.1.val := by rfl

private theorem keyParts_class (p : Parts) :
    (keyPartsEquiv p).toNat % B = p.2.2.val ∧ (keyNibble5 (keyPartsEquiv p)).val = p.2.1.val := by
  have hval := keyParts_toNat p
  have hq := p.2.1.isLt
  have hlow := p.2.2.isLt
  norm_num [B] at hval hlow
  constructor
  · change (keyPartsEquiv p).toNat % 1048576 = p.2.2.val
    omega
  · change ((keyPartsEquiv p).toNat / 1048576) % 16 = p.2.1.val
    omega

/-- The large 32-bit cardinality equals 256 times a cardinality in the
    16 × 2^20 coordinate plane. No actual BitVec enumeration occurs. -/
theorem keysAtWeight_card_eq_pairFiber (t : Nat) :
    (keysAtWeight t).card = 256 * (pairFiber t).card := by
  have hmem (p : Parts) :
      p ∈ ((Finset.univ : Finset Parts).filter
        (fun p => peakWeight p.2.1 p.2.2.val = t)) ↔
      keyPartsEquiv p ∈ keysAtWeight t := by
    have hk := keyParts_class p
    have hq : keyNibble5 (keyPartsEquiv p) = p.2.1 := Fin.ext hk.2
    simp only [keysAtWeight, Finset.mem_filter, Finset.mem_univ, true_and]
    change peakWeight p.2.1 p.2.2.val = t ↔
      peakWeight (keyNibble5 (keyPartsEquiv p))
        ((keyPartsEquiv p).toNat % B) = t
    rw [hq, hk.1]
  have hcard := Finset.card_equiv keyPartsEquiv hmem
  have hfiber :
      ((Finset.univ : Finset Parts).filter
        (fun p => peakWeight p.2.1 p.2.2.val = t)) =
        (Finset.univ : Finset (Fin 256)) ×ˢ pairFiber t := by
    ext p
    simp [pairFiber]
  rw [← hcard, hfiber, Finset.card_product]
  simp

/-! ## 2. A small combinatorial problem: fibers in Fin 16 × Fin B. -/

private def near (t : Nat) (ht : t < B) : Fin B :=
  ⟨t, ht⟩

private def far (t : Nat) (h0 : 0 < t) (ht : t < B) : Fin B :=
  ⟨B - t, by omega⟩

/-- The two V-shaped classes q=12,13 have two candidate prefixes,
    collapsing to one exactly at the midpoint B/2. -/
private def vCandidates (t : Nat) (h0 : 0 < t) (ht : t < B) :
    Finset (Fin B) :=
  if B ≤ 2 * t then {near t ht, far t h0 ht} else ∅

private theorem vCandidates_mem_iff (t : Nat) (h0 : 0 < t) (ht : t < B) (K : Fin B) :
    K ∈ vCandidates t h0 ht ↔ B ≤ 2 * t ∧ (K.val = t ∨ K.val = B - t) := by
  by_cases h : B ≤ 2 * t
  · simp [vCandidates, h, near, far, Fin.ext_iff]
  · simp [vCandidates, h]

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

private def middleModel (t : Nat) (h0 : 0 < t) (ht : t < B) : Finset (Fin 16 × Fin B) :=
  (({(7 : Fin 16)} : Finset (Fin 16)) ×ˢ {far t h0 ht}) ∪
    (({(8 : Fin 16)} : Finset (Fin 16)) ×ˢ {near t ht}) ∪
    (({(12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16)) ×ˢ vCandidates t h0 ht)

/-- A full characterization of the fiber, using only four possible
    values of q. Proof is a 16-case finite nibble calculation plus omega. -/
private theorem middle_fiber_eq
    (t : Nat) (h0 : 0 < t) (ht : t < B) :
    pairFiber t = middleModel t h0 ht := by
  ext p
  rcases p with ⟨q, K⟩
  have hK : K.val < B := K.isLt
  change K.val < 1048576 at hK
  change t < 1048576 at ht
  simp only [pairFiber, middleModel, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_product, Finset.mem_singleton,
    Finset.mem_insert]
  rw [vCandidates_mem_iff t h0 ht K]
  simp only [near, far, Fin.ext_iff]
  fin_cases q <;> simp [peakWeight_formula, B] <;> (try split_ifs) <;> omega

private theorem disjoint_products (a b : Finset (Fin 16)) (u v : Finset (Fin B))
    (hab : Disjoint a b) : Disjoint (a ×ˢ u) (b ×ˢ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨q, K⟩ hp hq
  exact (Finset.disjoint_left.mp hab) (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

private theorem middleModel_card (t : Nat) (h0 : 0 < t) (ht : t < B) :
    (middleModel t h0 ht).card = 2 + 2 * (vCandidates t h0 ht).card := by
  let A : Finset (Fin 16 × Fin B) := ({(7 : Fin 16)} : Finset (Fin 16)) ×ˢ {far t h0 ht}
  let C : Finset (Fin 16 × Fin B) := ({(8 : Fin 16)} : Finset (Fin 16)) ×ˢ {near t ht}
  let D : Finset (Fin 16 × Fin B) :=
    ({(12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16)) ×ˢ vCandidates t h0 ht
  have hac : Disjoint A C := disjoint_products _ _ _ _ (by decide)
  have had : Disjoint A D := disjoint_products _ _ _ _ (by decide)
  have hcd : Disjoint C D := disjoint_products _ _ _ _ (by decide)
  have hboth : Disjoint (A ∪ C) D := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.disjoint_left.mp had hx hy)
    · exact (Finset.disjoint_left.mp hcd hx hy)
  change (A ∪ C ∪ D).card = _
  rw [Finset.card_union_of_disjoint hboth, Finset.card_union_of_disjoint hac]
  have htwo : ({(12 : Fin 16), (13 : Fin 16)} : Finset (Fin 16)).card = 2 := by decide
  simp [A, C, D, Finset.card_product, htwo]

/-- Exact middle-fiber multiplicity before the 256 free high key bits. -/
theorem pairFiber_middle_card
    (t : Nat) (h0 : 0 < t) (ht : t < B) :
    (pairFiber t).card =
      if 2 * t < B then 2 else if 2 * t = B then 4 else 6 := by
  rw [middle_fiber_eq t h0 ht, middleModel_card,
    vCandidates_card]
  split_ifs <;> omega

/-! ## 3. Both endpoints, counted without enumerating Fin B. -/

private theorem pairFiber_zero_eq :
    pairFiber 0 = ({(8 : Fin 16)} : Finset (Fin 16)) ×ˢ {(0 : Fin B)} := by
  ext p
  rcases p with ⟨q, K⟩
  have hk := K.isLt
  change K.val < 1048576 at hk
  simp only [pairFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Finset.mem_singleton]
  fin_cases q <;> simp [peakWeight_formula, B] <;> (try split_ifs) <;> omega

theorem pairFiber_zero_card : (pairFiber 0).card = 1 := by
  rw [pairFiber_zero_eq]
  simp

private def regularQ : Finset (Fin 16) :=
  Finset.univ.filter (fun q => q.val ≠ 7 ∧ q.val ≠ 8 ∧ q.val ≠ 12 ∧ q.val ≠ 13)

private def specialQ : Finset (Fin 16) :=
  {(7 : Fin 16), (12 : Fin 16), (13 : Fin 16)}

private theorem pairFiber_top_eq :
    pairFiber B = (regularQ ×ˢ (Finset.univ : Finset (Fin B))) ∪ (specialQ ×ˢ {(0 : Fin B)}) := by
  ext p
  rcases p with ⟨q, K⟩
  have hk := K.isLt
  change K.val < 1048576 at hk
  simp only [pairFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_product, Finset.mem_singleton]
  simp only [regularQ, specialQ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases q <;> simp [peakWeight_formula, B] <;> (try split_ifs) <;> omega

/-- At the top weight, twelve q classes admit ALL B prefixes,
    and exactly three more pairs have prefix zero. -/
theorem pairFiber_top_card : (pairFiber B).card = 12 * B + 3 := by
  have hdisj : Disjoint regularQ specialQ := by
    apply Finset.disjoint_left.mpr
    intro q hreg hspec
    simp [regularQ, specialQ] at hreg hspec
    omega
  have hp : Disjoint
      (regularQ ×ˢ (Finset.univ : Finset (Fin B)))
      (specialQ ×ˢ {(0 : Fin B)}) :=
    disjoint_products _ _ _ _ hdisj
  have hr : regularQ.card = 12 := by decide
  have hs : specialQ.card = 3 := by decide
  rw [pairFiber_top_eq, Finset.card_union_of_disjoint hp]
  simp [Finset.card_product, hr, hs]

/-! ## 4. COMPLETE TRUE 32-bit key histogram. -/

/-- Exact multiplicity of EVERY possible maximum DDT, with
    `t = peakDDT / 512`. These are cardinalities of genuine BitVec 32
    keys, not of representative keys or of a sampled list. -/
theorem actual_key_peak_histogram (t : Nat) (ht : t ≤ B) :
    (keysAtWeight t).card =
      if t = 0 then 256
      else if 2 * t < B then 512
      else if 2 * t = B then 1024
      else if t < B then 1536
      else 3221226240 := by
  rw [keysAtWeight_card_eq_pairFiber]
  by_cases hzero : t = 0
  · subst t
    rw [pairFiber_zero_card]
    norm_num [B]
  by_cases htop : t = B
  · subst t
    rw [pairFiber_top_card]
    norm_num [B]
  have h0 : 0 < t := by omega
  have hB : t < B := by omega
  rw [pairFiber_middle_card t h0 hB]
  split_ifs <;> omega

/-- The previous cardinality theorem is recovered as the top endpoint. -/
theorem top_endpoint_again :
    (keysAtWeight B).card = 3221226240 := by
  simpa [B] using actual_key_peak_histogram B (le_refl B)

/-- Precisely 256 keys have zero one-hot DDT at EVERY input bit. -/
theorem zero_endpoint :
    (keysAtWeight 0).card = 256 := by
  simpa [B] using actual_key_peak_histogram 0 (by omega : 0 ≤ B)

/-- Numerical consistency check: the five frequency groups partition
    the entire 2^32-key space. The actual fiber cardinalities are
    established by `actual_key_peak_histogram` above. -/
theorem histogram_total_key_count :
    256 + 512 * (2 ^ 19 - 1) + 1024 +
      1536 * (2 ^ 19 - 1) + 3221226240 = 2 ^ 32 := by
  norm_num

end Magma.OneHotCompletePeakHistogram
