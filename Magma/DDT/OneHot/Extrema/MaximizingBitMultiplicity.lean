module

public import Magma.DDT.OneHot.Extrema.CompletePeakHistogram
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Multiplicity of maximizing one-bit input positions

For each 32-bit round key, `actualMaximizers` contains all one-bit input
positions attaining its best DDT count for output difference one. A positive
peak restricts this set to bits 20 through 23; a zero peak makes all 32
positions tie. Local coefficient masks determine the multiplicity.

The low twenty key bits split into zero, midpoint, and other nonzero
prefixes. Symbolic product counts give the distribution over actual keys:

| Maximizing positions | Keys |
| --- | --- |
| `1` | `2684352512` |
| `2` | `1342178048` |
| `3` | `268436224` |
| `4` | `256` |
| `32` | `256` |

These are all possible multiplicities, and the counts sum to `2^32`.
Only the sixteen key-nibble classes and four local bit positions are
evaluated; prefix and full-word cardinalities are handled symbolically.
-/

open scoped BigOperators

namespace Magma.OneHotMaximizingBitMultiplicity

open Magma.CarryAutomaton
open Magma.OneHotExactCoefficientMasks
open Magma.OneHotFixedKeyPeak
open Magma.OneHotKeyClasses
open Magma.OneHotFullKeyClassInvariant

private abbrev B : Nat :=
  2 ^ 20

private abbrev Parts :=
  Fin 256 × (Fin 16 × Fin B)

private theorem weight_formula (q : Fin 16) (K : Nat) (r : Fin 4) :
    weight q K r = (B - K) * coefficientBit q r + K * coefficientBit (nextNibble q) r := by rfl

private theorem peakWeight_formula (q : Fin 16) (K : Nat) :
    peakWeight q K =
      if q.val = 7 then B - K
      else
        if q.val = 8 then K
        else if q.val = 12 ∨ q.val = 13 then if 2 * K ≤ B then B - K else K else B := by
  rfl

/-- The four local positions that attain the true, key-specific maximum. -/
def activeMaximizers (q : Fin 16) (K : Nat) : Finset (Fin 4) :=
  Finset.univ.filter (fun r => weight q K r = peakWeight q K)

/-- ALL 32 positions attaining the true, key-specific maximum. -/
def actualMaximizers (k : (V 32)) : Finset (Fin 32) :=
  Finset.univ.filter (fun j =>
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) =
      2 ^ 9 * peakWeight (keyNibble5 k) (k.toNat % B))

/-- Four active positions, except that a zero maximum makes all 32
    positions tie. This function is purely a 16-by-4 mask computation. -/
def tieMultiplicity (q : Fin 16) (K : Nat) : Nat :=
  if peakWeight q K = 0 then 32 else (activeMaximizers q K).card

private theorem scale_eq (a b : Nat) : 2 ^ 9 * a = 2 ^ 9 * b ↔ a = b := by
  constructor
  · intro h; omega
  · rintro rfl; rfl

/-- Identify the actual 32-bit argmax set with the local 4-bit one.
    The exceptional all-zero DDT case is handled separately. -/
theorem actualMaximizers_card (k : (V 32)) :
    (actualMaximizers k).card =
      tieMultiplicity (keyNibble5 k) (k.toNat % B) := by
  let q := keyNibble5 k
  let K := k.toNat % B
  by_cases hz : peakWeight q K = 0
  · have hzero (j : Fin 32) :
        xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 := by
      have h := fixed_key_peak_bound k j
      change _ ≤ 2 ^ 9 * peakWeight q K at h
      rw [hz] at h
      omega
    have hfull : actualMaximizers k = Finset.univ := by
      unfold actualMaximizers
      apply Finset.filter_true_of_mem
      intro j _
      change xorDDT_g k _ _ = 2 ^ 9 * peakWeight q K
      rw [hzero j, hz]
      norm_num
    rw [hfull]
    have hz' : peakWeight (keyNibble5 k) (k.toNat % B) = 0 := hz
    simp [tieMultiplicity, hz']
  · have hcard : (activeMaximizers q K).card =
        (actualMaximizers k).card := by
      apply Finset.card_bij
        (fun r _ => (⟨20 + r.val, by omega⟩ : Fin 32))
      · intro r hr
        have heq : weight q K r = peakWeight q K :=
          (Finset.mem_filter.mp hr).2
        simp only [actualMaximizers, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [oneHot_g_DDT_exact_mask]
        exact (scale_eq _ _).mpr heq
      · intro r₁ _ r₂ _ h
        apply Fin.ext
        have hh := congrArg Fin.val h
        dsimp at hh
        omega
      · intro j hj
        have heq : xorDDT_g k
            (BitVec.ofNat 32 (2 ^ j.val)) (1#32) =
              2 ^ 9 * peakWeight q K := (Finset.mem_filter.mp hj).2
        have hm : 20 ≤ j.val ∧ j.val < 24 := by
          by_contra hn
          have hout : j.val < 20 ∨ 24 ≤ j.val := by omega
          have hzero := oneHot_outside_middle_zero k j hout
          change xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 0 at hzero
          rw [hzero] at heq
          have hp : 0 < peakWeight q K := Nat.pos_of_ne_zero hz
          omega
        let r : Fin 4 := ⟨j.val - 20, by omega⟩
        have hjval : j.val = 20 + r.val := by dsimp [r]; omega
        have hweight : weight q K r = peakWeight q K := by
          rw [hjval, oneHot_g_DDT_exact_mask] at heq
          exact (scale_eq _ _).mp heq
        refine ⟨r, ?_, Fin.ext ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hweight⟩
        · exact hjval.symm
    rw [← hcard]
    have hz' : peakWeight (keyNibble5 k) (k.toNat % B) ≠ 0 := hz
    simp [tieMultiplicity, hz']
    rfl

/-- A word has zero best one-hot DDT precisely in the previously
    proved exceptional key class; here all 32 positions maximize. -/
theorem zero_peak_has_32_maximizers (k : (V 32))
    (hzero : peakWeight (keyNibble5 k) (k.toNat % B) = 0) :
    (actualMaximizers k).card = 32 := by
  rw [actualMaximizers_card]
  simp [tieMultiplicity, hzero]

/-! ### Small finite tables in the three prefix regimes. -/

private def half : Fin B :=
  ⟨B / 2, by norm_num [B]⟩

private def qAtZero (n : Nat) : Finset (Fin 16) :=
  Finset.univ.filter (fun q => tieMultiplicity q 0 = n)

private def qAtHalf (n : Nat) : Finset (Fin 16) :=
  Finset.univ.filter (fun q => tieMultiplicity q (B / 2) = n)

private def qGeneric (n : Nat) : Finset (Fin 16) :=
  Finset.univ.filter (fun q => tieMultiplicity q 1 = n)

/-- Exact sixteen-class multiplicities at a zero lower-key prefix. -/
theorem zero_regime_small_counts :
    (qAtZero 1).card = 4 ∧ (qAtZero 2).card = 6 ∧
    (qAtZero 3).card = 4 ∧ (qAtZero 4).card = 1 ∧
    (qAtZero 32).card = 1 := by decide

/-- At the one exceptional midpoint two maximizing positions tie in
    the V-shaped q=12 and q=13 classes. -/
theorem half_regime_small_counts :
    (qAtHalf 1).card = 8 ∧ (qAtHalf 2).card = 7 ∧
    (qAtHalf 3).card = 1 := by decide

/-- All other nonzero low prefixes have the same counts, regardless
    of which side of the midpoint they lie on. -/
theorem generic_regime_small_counts :
    (qGeneric 1).card = 10 ∧ (qGeneric 2).card = 5 ∧
    (qGeneric 3).card = 1 := by decide

/-- Outside {1,2,3,4,32}, no multiplicity is possible even locally. -/
private theorem small_ties_only (q : Fin 16) :
    (tieMultiplicity q 0 ∈ ({1, 2, 3, 4, 32} : Finset Nat)) ∧
    (tieMultiplicity q (B / 2) ∈ ({1, 2, 3} : Finset Nat)) ∧
    (tieMultiplicity q 1 ∈ ({1, 2, 3} : Finset Nat)) := by
  fin_cases q <;> decide

/-- SYMBOLIC reduction to three regimes. Does not iterate over Fin B.
    Only the sixteen four-bit masks are unfolded. -/
theorem tieMultiplicity_regimes (q : Fin 16) (K : Nat) (hK : K < B) :
    tieMultiplicity q K =
      if K = 0 then tieMultiplicity q 0
      else if 2 * K = B then tieMultiplicity q (B / 2)
      else tieMultiplicity q 1 := by
  change K < 1048576 at hK
  by_cases hzero : K = 0
  · subst K
    simp
  by_cases hmid : 2 * K = B
  · have hkhalf : K = B / 2 := by omega
    rw [hkhalf]
    simp [B]
  · have hpositive : 0 < K := by omega
    -- The count of argmax bits is constant away from K=0 and K=B/2.
    -- In the two V-shaped classes its POSITION may change, but its
    -- MULTIPLICITY does not.
    simp only [ite_eq_right hzero, ite_eq_right hmid]
    have hu : (Finset.univ : Finset (Fin 4)) =
        ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
    change 2 * K ≠ 1048576 at hmid
    have hKB : K ≠ 1048576 := by omega
    have hsub0 : 1048576 - K ≠ 0 := by omega
    have hsubB : 1048576 - K ≠ 1048576 := by omega
    have hsum : 1048576 - K + K = 1048576 := by omega
    have hsubK : 1048576 - K ≠ K := by omega
    by_cases hside : 2 * K ≤ 1048576 <;> fin_cases q <;>
      simp [tieMultiplicity, activeMaximizers, hu, weight_formula,
        peakWeight_formula, coefficientBit, coefficientMask, nextNibble, B,
        Finset.filter_insert, Finset.filter_singleton, hside, hzero,
        hKB, hsub0, hsubB, hsum, hsubK, Ne.symm hsubK, Ne.symm hsub0, Ne.symm hzero]

/-! ### Counting actual 32-bit keys by a product equivalence. -/

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

/-- Actual words grouped by the number of attaining positions. -/
def keysWithTies (n : Nat) : Finset (V 32) :=
  Finset.univ.filter (fun k => (actualMaximizers k).card = n)

private def pairFiber (n : Nat) : Finset (Fin 16 × Fin B) :=
  Finset.univ.filter (fun p => tieMultiplicity p.1 p.2.val = n)

private theorem real_keys_card_eq_fiber (n : Nat) :
    (keysWithTies n).card = 256 * (pairFiber n).card := by
  have hmem (p : Parts) :
    p ∈ ((Finset.univ : Finset Parts).filter (fun p => tieMultiplicity p.2.1 p.2.2.val = n)) ↔
      keyPartsEquiv p ∈ keysWithTies n := by
    have hk := keyParts_class p
    have hq : keyNibble5 (keyPartsEquiv p) = p.2.1 := Fin.ext hk.2
    simp only [keysWithTies, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [actualMaximizers_card, hq, hk.1]
  have hcard := Finset.card_equiv keyPartsEquiv hmem
  have hfiber :
    ((Finset.univ : Finset Parts).filter (fun p => tieMultiplicity p.2.1 p.2.2.val = n)) =
      (Finset.univ : Finset (Fin 256)) ×ˢ pairFiber n := by
    ext p
    simp [pairFiber]
  rw [← hcard, hfiber, Finset.card_product]
  simp

private def otherLow : Finset (Fin B) :=
  ((Finset.univ : Finset (Fin B)).erase 0).erase half

private theorem otherLow_card : otherLow.card = B - 2 := by
  have hne : half ≠ (0 : Fin B) := by decide
  have hmem : half ∈ ((Finset.univ : Finset (Fin B)).erase 0) := by simp [hne]
  unfold otherLow
  rw [Finset.card_erase_of_mem hmem]
  rw [Finset.card_erase_of_mem (by simp : (0 : Fin B) ∈ (Finset.univ : Finset (Fin B)))]
  simp [B]

private def pairModel (n : Nat) : Finset (Fin 16 × Fin B) :=
  (qAtZero n ×ˢ {(0 : Fin B)}) ∪ (qAtHalf n ×ˢ {half}) ∪ (qGeneric n ×ˢ otherLow)

private theorem fiber_eq_model (n : Nat) : pairFiber n = pairModel n := by
  ext p
  rcases p with ⟨q, K⟩
  have hK : K.val < B := K.isLt
  have hreg := tieMultiplicity_regimes q K.val hK
  simp only [pairFiber, pairModel, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_product, Finset.mem_singleton]
  by_cases hz : K = (0 : Fin B)
  · subst K
    simp [qAtZero, qAtHalf, qGeneric, otherLow, half, B]
  by_cases hm : K = half
  · subst K
    simp [qAtZero, qAtHalf, qGeneric, otherLow, half, B]
  · have hzval : K.val ≠ 0 := by
      intro h; exact hz (Fin.ext h)
    have hmval : 2 * K.val ≠ B := by
      intro h
      apply hm
      apply Fin.ext
      change K.val = B / 2
      omega
    have hother : K ∈ otherLow := by simp [otherLow, hz, hm]
    rw [hreg]
    simp [hzval, hmval, qGeneric, hother, hz, hm]

private theorem pairModel_card (n : Nat) :
    (pairModel n).card = (qAtZero n).card + (qAtHalf n).card + (B - 2) * (qGeneric n).card := by
  let A := qAtZero n ×ˢ {(0 : Fin B)}
  let C := qAtHalf n ×ˢ {half}
  let D := qGeneric n ×ˢ otherLow
  have hhalfnz : half ≠ (0 : Fin B) := by decide
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro p hp hc
    have h0 := (Finset.mem_product.mp hp).2
    have hh := (Finset.mem_product.mp hc).2
    have hp0 := Finset.mem_singleton.mp h0
    have hph := Finset.mem_singleton.mp hh
    exact hhalfnz (hph.symm.trans hp0)
  have hAD : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro p hp hd
    have hp0 := Finset.mem_singleton.mp (Finset.mem_product.mp hp).2
    have hn : p.2 ≠ 0 := by
      have h := (Finset.mem_product.mp hd).2
      simp [otherLow] at h
      exact h.2
    exact hn hp0
  have hCD : Disjoint C D := by
    apply Finset.disjoint_left.mpr
    intro p hp hd
    have hph := Finset.mem_singleton.mp (Finset.mem_product.mp hp).2
    have hn : p.2 ≠ half := by
      have h := (Finset.mem_product.mp hd).2
      simp [otherLow] at h
      exact h.1
    exact hn hph
  have hboth : Disjoint (A ∪ C) D := by
    apply Finset.disjoint_left.mpr
    intro p hp hd
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp hAD hp hd)
    · exact (Finset.disjoint_left.mp hCD hp hd)
  change (A ∪ C ∪ D).card = _
  rw [Finset.card_union_of_disjoint hboth, Finset.card_union_of_disjoint hAC]
  simp [A, C, D, otherLow_card, Nat.mul_comm]

/-- The counting theorem is valid for ANY multiplicity n. Everything
    expensive has been reduced to finite subsets of Fin 16. -/
theorem actual_key_tie_count_general (n : Nat) :
    (keysWithTies n).card =
      256 * ((qAtZero n).card + (qAtHalf n).card +
        (B - 2) * (qGeneric n).card) := by
  rw [real_keys_card_eq_fiber, fiber_eq_model, pairModel_card]

/-- Exactly 2,684,352,512 keys have a UNIQUE maximizing input bit. -/
theorem actual_key_one_maximizing_bit :
    (keysWithTies 1).card = 2684352512 := by
  rw [actual_key_tie_count_general]
  have a := zero_regime_small_counts.1
  have b := half_regime_small_counts.1
  have c := generic_regime_small_counts.1
  rw [a, b, c]
  norm_num [B]

/-- Exactly 1,342,178,048 keys have TWO maximizing input bits. -/
theorem actual_key_two_maximizing_bits :
    (keysWithTies 2).card = 1342178048 := by
  rw [actual_key_tie_count_general]
  have a := zero_regime_small_counts.2.1
  have b := half_regime_small_counts.2.1
  have c := generic_regime_small_counts.2.1
  rw [a, b, c]
  norm_num [B]

/-- Exactly 268,436,224 keys have THREE maximizing input bits. -/
theorem actual_key_three_maximizing_bits :
    (keysWithTies 3).card = 268436224 := by
  rw [actual_key_tie_count_general]
  have a := zero_regime_small_counts.2.2.1
  have b := half_regime_small_counts.2.2
  have c := generic_regime_small_counts.2.2
  rw [a, b, c]
  norm_num [B]

/-- Four-way tie: q=3, K=0, with free upper eight key bits. -/
theorem actual_key_four_maximizing_bits :
    (keysWithTies 4).card = 256 := by
  rw [actual_key_tie_count_general]
  have a := zero_regime_small_counts.2.2.2.1
  have b : (qAtHalf 4).card = 0 := by decide
  have c : (qGeneric 4).card = 0 := by decide
  rw [a, b, c]
  norm_num [B]

/-- All 32 bits tie only when the maximum is zero: q=8, K=0. -/
theorem actual_key_all_32_maximizing_bits :
    (keysWithTies 32).card = 256 := by
  rw [actual_key_tie_count_general]
  have a := zero_regime_small_counts.2.2.2.2
  have b : (qAtHalf 32).card = 0 := by decide
  have c : (qGeneric 32).card = 0 := by decide
  rw [a, b, c]
  norm_num [B]

/-- At every key the number of maximizing positions is one of
    1,2,3,4,32. The last case has a zero best DDT. -/
theorem all_tie_multiplicities (k : (V 32)) :
    (actualMaximizers k).card ∈ ({1, 2, 3, 4, 32} : Finset Nat) := by
  rw [actualMaximizers_card]
  let q := keyNibble5 k
  let K := k.toNat % B
  have hK : K < B := Nat.mod_lt _ (by norm_num [B])
  have hsmall : ({1, 2, 3} : Finset Nat) ⊆
      ({1, 2, 3, 4, 32} : Finset Nat) := by decide
  rw [tieMultiplicity_regimes q K hK]
  by_cases hz : K = 0
  · simpa [hz] using (small_ties_only q).1
  · by_cases hm : 2 * K = B
    · have hh := hsmall (small_ties_only q).2.1
      simpa [hz, hm] using hh
    · have hh := hsmall (small_ties_only q).2.2
      simpa [hz, hm] using hh

/-- Sanity-check: the disjoint key multiplicities sum to 2^32. -/
theorem tie_histogram_total :
    2684352512 + 1342178048 + 268436224 + 256 + 256 = 2 ^ 32 := by
  norm_num

end Magma.OneHotMaximizingBitMultiplicity
