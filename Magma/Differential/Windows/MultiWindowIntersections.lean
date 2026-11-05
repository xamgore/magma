module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ArbitraryWindowIntersections

@[expose] public section

/-!
# Arbitrary finite families of three-round window constraints

Each rule records a 3-round window and two predicates, one on the first
and one on the third round key. The same source word can appear in any
number of rules. We intersect all predicates that refer to each of the
eight source slots, then count each source word once.

The proof constructs a single equivalence between constrained master keys
and a dependent product of eight constrained 32-bit words. Reused source
slots contribute intersections of their local conditions.
-/

namespace Magma.DiffanMultiWindowIntersections

open Magma
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanArbitraryWindowIntersections
open Magma.DiffanRepeatedWindowIntersections
open Magma.DiffanOuterKeySplitCertificate

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- One window and its two local conditions, attached to the first and
    third round keys in that window. Lists may contain repeated windows. -/
abbrev WindowRule := Fin 30 × (Word → Prop) × (Word → Prop)

/-- All rules hold for one and the SAME 256-bit master key. -/
def allWindowConditions (rules : List WindowRule) (K : Master) : Prop :=
  ∀ r, r ∈ rules → pairCondition r.1 r.2.1 r.2.2 K

/-- Each of the eight master-key source words satisfies every predicate
    whose window accesses that particular source slot. -/
def slotConditionMany (rules : List WindowRule) (i : Fin 8)
    (w : Word) : Prop :=
  ∀ r, r ∈ rules →
    (i = firstSlot r.1 → r.2.1 w) ∧
    (i = thirdSlot r.1 → r.2.2 w)

/-- Reuse the real key schedule, not independent nominal round keys. -/
private theorem rule_iff_tuple (r : WindowRule) (K : Master) :
    pairCondition r.1 r.2.1 r.2.2 K ↔
      r.2.1 ((eightWordsEquiv K) (firstSlot r.1)) ∧
      r.2.2 ((eightWordsEquiv K) (thirdSlot r.1)) := by
  unfold pairCondition
  simp only [roundKey_eq_source]
  rfl

private theorem all_iff_tuple (rules : List WindowRule) (K : Master) :
    allWindowConditions rules K ↔
      ∀ r,
        r ∈ rules →
          r.2.1 ((eightWordsEquiv K) (firstSlot r.1)) ∧
            r.2.2 ((eightWordsEquiv K) (thirdSlot r.1)) := by
  constructor
  · intro h r hr
    exact (rule_iff_tuple r K).mp (h r hr)
  · intro h r hr
    exact (rule_iff_tuple r K).mpr (h r hr)

/-- Each rule on the tuple is equivalent to the family of local
    restrictions, even when many rules reuse the same slot. -/
private theorem tuple_iff_slots (rules : List WindowRule)
    (f : Fin 8 → Word) :
    (∀ r, r ∈ rules →
      r.2.1 (f (firstSlot r.1)) ∧
      r.2.2 (f (thirdSlot r.1))) ↔
      ∀ i : Fin 8, slotConditionMany rules i (f i) := by
  constructor
  · intro h i r hr
    obtain ⟨hp, hq⟩ := h r hr
    constructor
    · intro hi
      cases hi
      exact hp
    · intro hi
      cases hi
      exact hq
  · intro h r hr
    exact ⟨((h (firstSlot r.1)) r hr).1 rfl,
      ((h (thirdSlot r.1)) r hr).2 rfl⟩

/-- Constrained master keys correspond to source words satisfying all
    local conditions attached to their slots. -/
def allWindowFiberEquiv (rules : List WindowRule) :
    {K : Master // allWindowConditions rules K} ≃
      ((i : Fin 8) → {w : Word // slotConditionMany rules i w}) where
  toFun := fun ⟨K, hK⟩ i =>
    ⟨(eightWordsEquiv K) i,
      ((tuple_iff_slots rules (eightWordsEquiv K)).mp
        ((all_iff_tuple rules K).mp hK)) i⟩
  invFun := fun g =>
    ⟨eightWordsEquiv.symm (fun i => (g i).1),
      (all_iff_tuple rules (eightWordsEquiv.symm (fun i => (g i).1))).mpr
        (by
          have htuple : ∀ r, r ∈ rules →
              r.2.1 ((fun i => (g i).1) (firstSlot r.1)) ∧
              r.2.2 ((fun i => (g i).1) (thirdSlot r.1)) :=
            (tuple_iff_slots rules (fun i => (g i).1)).mpr
              (fun i => (g i).2)
          simpa only [Equiv.apply_symm_apply] using htuple)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact eightWordsEquiv.symm_apply_apply x.1
  right_inv := by
    intro g
    funext i
    apply Subtype.ext
    exact congrFun (eightWordsEquiv.apply_symm_apply (fun i => (g i).1)) i

open scoped Classical in
/-- Exact master-key count for a finite list of windows, including
    repeated and crossed source slots. -/
theorem allWindowConditions_card (rules : List WindowRule) :
    Fintype.card {K : Master // allWindowConditions rules K} =
      ∏ i : Fin 8, Fintype.card
        {w : Word // slotConditionMany rules i w} := by
  classical
  calc
    Fintype.card {K : Master // allWindowConditions rules K} =
      Fintype.card
        ((i : Fin 8) → {w : Word // slotConditionMany rules i w}) :=
      Fintype.card_congr (allWindowFiberEquiv rules)
    _ = _ := Fintype.card_pi

/-- Combining two batches is conjunction, on one shared master key. -/
theorem allWindowConditions_append
    (a b : List WindowRule) (K : Master) :
    allWindowConditions (a ++ b) K ↔
      allWindowConditions a K ∧ allWindowConditions b K := by
  constructor
  · intro h
    constructor
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inl hr))
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inr hr))
  · rintro ⟨ha, hb⟩ r hr
    rcases List.mem_append.mp hr with h₁ | h₂
    · exact ha r h₁
    · exact hb r h₂

/-- A contradiction at ANY one source slot excludes every master key,
    without evaluating the corresponding local set or the entire cipher. -/
theorem no_master_of_impossible_slot
    (rules : List WindowRule) (i : Fin 8)
    (h : ∀ w : Word, ¬ slotConditionMany rules i w) :
    ∀ K : Master, ¬ allWindowConditions rules K := by
  intro K hK
  have ht := (all_iff_tuple rules K).mp hK
  have hs := (tuple_iff_slots rules (eightWordsEquiv K)).mp ht
  exact h ((eightWordsEquiv K) i) (hs i)

end Magma.DiffanMultiWindowIntersections
