module

public import Magma.DDT.OneHot.Extrema.FixedKeyPeak
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Cardinalities of the actual maximizing and nonmaximizing round keys

A bijection decomposes every 32-bit key into eight high bits, key nibble
five, and the low twenty bits. The proved full-word DDT classification
identifies maximizing keys with a disjoint union of products: fifteen
nibble choices at low prefix zero, and twelve at any nonzero prefix.

Counting these products gives `3221226240` actual keys whose one-bit-input,
output-one DDT reaches `2^29`, and `1073741056` keys that do not. The
cardinalities concern subsets of full 32-bit words, with all prefix and
word counts handled symbolically rather than by enumeration.
-/

open scoped BigOperators

namespace Magma.OneHotActualKeyCardinality

open Magma.CarryAutomaton
open Magma.OneHotKeyClasses
open Magma.OneHotFixedKeyPeak

private abbrev B : Nat :=
  2 ^ 20

private abbrev Parts :=
  Fin 256 × (Fin 16 × Fin B)

/-! ## 1. A genuine bijection, not a simulated key sample. -/

/-- Split the 32-bit word into exactly 8+4+20 bits. The two
    `finProdFinEquiv` maps encode (a,b) by b + size(b)*a. -/
private def keyPartsEquiv : Parts ≃ V 32 := by
  let e₁ : Parts ≃ Fin (256 * (16 * B)) :=
    (Equiv.prodCongr (Equiv.refl (Fin 256))
      (finProdFinEquiv : Fin 16 × Fin B ≃ Fin (16 * B))).trans
      (finProdFinEquiv : Fin 256 × Fin (16 * B) ≃ Fin (256 * (16 * B)))
  have hsize : 256 * (16 * B) = 2 ^ 32 := by norm_num [B]
  let e₂ : Fin (256 * (16 * B)) ≃ V 32 :=
    (finCongr hsize).trans (BitVec.equivFin (m := 32)).toEquiv.symm
  exact e₁.trans e₂

/-- The unsigned value of a word reconstructed from the three pieces. -/
private theorem keyPartsEquiv_toNat (p : Parts) :
    (keyPartsEquiv p).toNat =
      p.2.2.val + B * p.2.1.val + (16 * B) * p.1.val := by
  rfl

/-- The classification invariants of a reconstructed word are exactly
    its second and third components. -/
private theorem keyParts_class (p : Parts) :
    (keyPartsEquiv p).toNat % B = p.2.2.val ∧
    (keyNibble5 (keyPartsEquiv p)).val = p.2.1.val := by
  have hval := keyPartsEquiv_toNat p
  have hq : p.2.1.val < 16 := p.2.1.isLt
  have hlow : p.2.2.val < B := p.2.2.isLt
  norm_num [B] at hval hlow
  constructor
  · change (keyPartsEquiv p).toNat % 1048576 = p.2.2.val
    omega
  · change ((keyPartsEquiv p).toNat / 1048576) % 16 = p.2.1.val
    omega

/-! ## 2. Count disjoint products of small sets. -/

private def goodZero : Finset (Fin 16) :=
  Finset.univ.filter (fun q => q.val ≠ 8)

private def goodNonzero : Finset (Fin 16) :=
  Finset.univ.filter (fun q => q.val ≠ 7 ∧ q.val ≠ 8 ∧ q.val ≠ 12 ∧ q.val ≠ 13)

private def nonzeroLow : Finset (Fin B) :=
  Finset.univ.erase 0

/-- Precisely the (q,low) pairs which reach 2^29. -/
private def goodPairs : Finset (Fin 16 × Fin B) :=
  (goodZero ×ˢ {(0 : Fin B)}) ∪
  (goodNonzero ×ˢ nonzeroLow)

private def goodTriples : Finset Parts :=
  (Finset.univ : Finset (Fin 256)) ×ˢ goodPairs

private theorem mem_goodPairs (q : Fin 16) (low : Fin B) :
    (q, low) ∈ goodPairs ↔
      if low.val = 0 then q.val ≠ 8 else q.val ≠ 7 ∧ q.val ≠ 8 ∧ q.val ≠ 12 ∧ q.val ≠ 13 := by
  by_cases hlow : low.val = 0
  · have hz : low = (0 : Fin B) := Fin.ext hlow
    subst low
    simp [goodPairs, goodZero, goodNonzero, nonzeroLow]
  · have hn : low ≠ (0 : Fin B) := by
      intro h
      apply hlow
      simp [h]
    simp [goodPairs, goodZero, goodNonzero, nonzeroLow, hlow, hn, Ne.symm hn]

private theorem mem_goodTriples (p : Parts) :
    p ∈ goodTriples ↔
      if p.2.2.val = 0 then p.2.1.val ≠ 8
      else p.2.1.val ≠ 7 ∧ p.2.1.val ≠ 8 ∧ p.2.1.val ≠ 12 ∧ p.2.1.val ≠ 13 := by
  simp only [goodTriples, Finset.mem_product, Finset.mem_univ, true_and]
  exact mem_goodPairs p.2.1 p.2.2

private theorem card_goodPairs : goodPairs.card = 15 + 12 * (B - 1) := by
  have hz : goodZero.card = 15 := by decide
  have hn : goodNonzero.card = 12 := by decide
  have hl : nonzeroLow.card = B - 1 := by
    unfold nonzeroLow
    rw [Finset.card_erase_of_mem (by simp : (0 : Fin B) ∈ (Finset.univ : Finset (Fin B)))]
    simp
  have hd : Disjoint (goodZero ×ˢ {(0 : Fin B)}) (goodNonzero ×ˢ nonzeroLow) := by
    apply Finset.disjoint_left.mpr
    intro p hp₀ hp₁
    have hzero : p.2 = (0 : Fin B) := Finset.mem_singleton.mp (Finset.mem_product.mp hp₀).2
    have hnonzero : p.2 ≠ (0 : Fin B) := (Finset.mem_erase.mp (Finset.mem_product.mp hp₁).2).1
    exact hnonzero hzero
  rw [goodPairs, Finset.card_union_of_disjoint hd]
  simp [Finset.card_product, hz, hn, hl]

private theorem card_goodTriples : goodTriples.card = 3221226240 := by
  unfold goodTriples
  rw [Finset.card_product, card_goodPairs]
  norm_num [B]

/-! ## 3. True cardinality over all BitVec 32 keys. -/

/-- The FINSET of real keys which attain the one-hot global DDT peak. -/
def maximizingKeys : Finset (V 32) :=
  Finset.univ.filter (fun k =>
    ∃ j : Fin 32,
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) = 2 ^ 29)

/-- The combinatorial good-triplet set is EXACTLY the preimage of the
    actual Magma DDT-maximizing keys under the key decomposition. -/
theorem keyParts_maximizer_iff (p : Parts) :
    p ∈ goodTriples ↔ keyPartsEquiv p ∈ maximizingKeys := by
  simp only [maximizingKeys, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_goodTriples, real_key_attains_iff_class]
  rw [(keyParts_class p).1, (keyParts_class p).2]

/-- Exact REAL key count; unlike the previous arithmetic count, the
    LHS is the cardinality of the subset of actual 32-bit words. -/
theorem actual_maximizing_keys_card :
    maximizingKeys.card = 3221226240 := by
  have hcard : goodTriples.card = maximizingKeys.card :=
    Finset.card_equiv keyPartsEquiv keyParts_maximizer_iff
  rw [← hcard]
  exact card_goodTriples

/-- There are exactly 2^32 - 3221226240 words not achieving the peak. -/
theorem actual_nonmaximizing_keys_card :
    ((Finset.univ : Finset (V 32)) \ maximizingKeys).card = 1073741056 := by
  have hsub : maximizingKeys ⊆ (Finset.univ : Finset (V 32)) := by
    intro k _; simp
  have hcard : Fintype.card (V 32) = 2 ^ 32 := by
    rw [← FinEnum.card_eq_fintypeCard]
    exact FinEnum.card_bitVec 32
  rw [Finset.card_sdiff_of_subset hsub, actual_maximizing_keys_card,
    Finset.card_univ, hcard]
  norm_num

end Magma.OneHotActualKeyCardinality
