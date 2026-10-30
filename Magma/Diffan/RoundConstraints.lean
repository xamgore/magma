module

import all Init.Data.Range.Basic
public import Magma.Diffan.MultiWindowIntersections

@[expose] public section

/-!
# Round-indexed key constraints for the Magma schedule

A rule constrains the 32-bit round key at any position in the 32-round
ordinary-G schedule. The RFC 8891 key schedule maps these positions to
eight source words of the same 256-bit master key. Predicates referring
to the same source word are intersected before local cardinalities are
multiplied.

The resulting count applies to finite lists of unary key predicates.
An equivalence identifies constrained master keys with a dependent product
of eight constrained source words. Three-round window rules translate to
this representation by constraining their first and third round keys.
-/

namespace Magma.DiffanRoundConstraints

open Magma
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanOuterKeySplitCertificate
open Magma.DiffanRepeatedWindowIntersections
open Magma.DiffanMultiWindowIntersections

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- A condition on the key word used at ONE of the 32 round positions.
    A list of rules may mention the same position many times. -/
abbrev RoundRule := Fin 32 × (Word → Prop)

/-- A single master key must satisfy every rule in the finite list. -/
def allRoundConditions (rules : List RoundRule) (K : Master) : Prop :=
  ∀ r, r ∈ rules → r.2 (roundKey K r.1)

/-- Gather *all* requirements on source word i, including repeats and
    cross-round aliases induced by the real key schedule. -/
def slotConditionRounds (rules : List RoundRule) (i : Fin 8)
    (w : Word) : Prop :=
  ∀ r, r ∈ rules → sourceSlot r.1 = i → r.2 w

/-- Transport one predicate through the actual base-key representation. -/
private theorem rule_iff_tuple (r : RoundRule) (K : Master) :
    r.2 (roundKey K r.1) ↔
      r.2 ((eightWordsEquiv K) (sourceSlot r.1)) := by
  rw [roundKey_eq_source]
  rfl

private theorem all_iff_tuple (rules : List RoundRule) (K : Master) :
    allRoundConditions rules K ↔ ∀ r, r ∈ rules → r.2 ((eightWordsEquiv K) (sourceSlot r.1)) := by
  constructor
  · intro h r hr
    exact (rule_iff_tuple r K).mp (h r hr)
  · intro h r hr
    exact (rule_iff_tuple r K).mpr (h r hr)

/-- Round conditions on the eight-word tuple agree with the conjunction
    of the local conditions on its individual source-word slots. -/
private theorem tuple_iff_slots (rules : List RoundRule)
    (f : Fin 8 → Word) :
    (∀ r, r ∈ rules → r.2 (f (sourceSlot r.1))) ↔
      ∀ i : Fin 8, slotConditionRounds rules i (f i) := by
  constructor
  · intro h i r hr hi
    simpa only [hi] using h r hr
  · intro h r hr
    exact h (sourceSlot r.1) r hr rfl

/-- The actual constrained 256-bit master-key fiber is equivalent to a
    product of eight separately constrained 32-bit word fibers.
    This is stronger than an equality of cardinalities. -/
def allRoundFiberEquiv (rules : List RoundRule) :
    {K : Master // allRoundConditions rules K} ≃
      ((i : Fin 8) → {w : Word // slotConditionRounds rules i w}) where
  toFun := fun ⟨K, hK⟩ i =>
    ⟨(eightWordsEquiv K) i,
      ((tuple_iff_slots rules (eightWordsEquiv K)).mp
        ((all_iff_tuple rules K).mp hK)) i⟩
  invFun := fun g =>
    ⟨eightWordsEquiv.symm (fun i => (g i).1),
      (all_iff_tuple rules (eightWordsEquiv.symm (fun i => (g i).1))).mpr
        (by
          have ht : ∀ r, r ∈ rules →
              r.2 ((fun i => (g i).1) (sourceSlot r.1)) :=
            (tuple_iff_slots rules (fun i => (g i).1)).mpr
              (fun i => (g i).2)
          simpa only [Equiv.apply_symm_apply] using ht)⟩
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
/-- Exact cardinality for any finite batch of local round-key constraints
    on the complete 32-round Magma schedule. Repeated subkeys are never
    treated as independent variables. -/
theorem allRoundConditions_card (rules : List RoundRule) :
    Fintype.card {K : Master // allRoundConditions rules K} =
      ∏ i : Fin 8, Fintype.card
        {w : Word // slotConditionRounds rules i w} := by
  classical
  calc
    Fintype.card {K : Master // allRoundConditions rules K} =
        Fintype.card
          ((i : Fin 8) → {w : Word // slotConditionRounds rules i w}) :=
      Fintype.card_congr (allRoundFiberEquiv rules)
    _ = _ := Fintype.card_pi

/-- Appending a second batch means INTERSECTING key requirements,
    not multiplying counts of the batches. -/
theorem allRoundConditions_append
    (a b : List RoundRule) (K : Master) :
    allRoundConditions (a ++ b) K ↔
      allRoundConditions a K ∧ allRoundConditions b K := by
  constructor
  · intro h
    constructor
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inl hr))
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inr hr))
  · rintro ⟨ha, hb⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ha r hr
    · exact hb r hr

/-- Source-slot constraints also intersect when batches are appended;
    the identity is pointwise and preserves all reused-key dependencies. -/
theorem slotConditionRounds_append
    (a b : List RoundRule) (i : Fin 8) (w : Word) :
    slotConditionRounds (a ++ b) i w ↔
      slotConditionRounds a i w ∧ slotConditionRounds b i w := by
  constructor
  · intro h
    constructor
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inl hr))
    · intro r hr
      exact h r (List.mem_append.mpr (Or.inr hr))
  · rintro ⟨ha, hb⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ha r hr
    · exact hb r hr

/-- If one source-word fiber is empty, no master key can satisfy the
    entire collection of round-key restrictions. -/
theorem no_master_of_impossible_slot
    (rules : List RoundRule) (i : Fin 8)
    (h : ∀ w : Word, ¬ slotConditionRounds rules i w) :
    ∀ K : Master, ¬ allRoundConditions rules K := by
  intro K hK
  have ht := (all_iff_tuple rules K).mp hK
  have hs := (tuple_iff_slots rules (eightWordsEquiv K)).mp ht
  exact h ((eightWordsEquiv K) i) (hs i)

/-! ## Three-round window constraints -/

/-- Express a three-round window constraint as two unary rules:
    one at its first round, another at its third round. The key schedule
    itself will automatically identify reused source words. -/
def windowToRoundRules (r : WindowRule) : List RoundRule :=
  [(⟨r.1.val, by omega⟩, r.2.1),
   (⟨r.1.val + 2, by omega⟩, r.2.2)]

/-- Collect the first- and third-round key constraints from each window. -/
def windowsToRoundRules : List WindowRule → List RoundRule
  | [] => []
  | r :: rs => windowToRoundRules r ++ windowsToRoundRules rs

private theorem windowToRoundRules_iff (r : WindowRule) (K : Master) :
    allRoundConditions (windowToRoundRules r) K ↔ pairCondition r.1 r.2.1 r.2.2 K := by
  constructor
  · intro h
    exact
      ⟨h (⟨r.1.val, by omega⟩, r.2.1) (by simp [windowToRoundRules]),
        h (⟨r.1.val + 2, by omega⟩, r.2.2) (by simp [windowToRoundRules])⟩
  · intro h q hq
    have hmem : q = (⟨r.1.val, by omega⟩, r.2.1) ∨ q = (⟨r.1.val + 2, by omega⟩, r.2.2) := by
      simpa [windowToRoundRules] using hq
    rcases hmem with heq | heq
    · cases heq
      exact h.1
    · cases heq
      exact h.2

/-- Window constraints and their round-indexed representation select
    the same master keys. -/
theorem windowsToRoundRules_correct (rules : List WindowRule)
    (K : Master) :
    allRoundConditions (windowsToRoundRules rules) K ↔
      allWindowConditions rules K := by
  induction rules with
  | nil =>
      constructor
      · intro _ r hr
        cases hr
      · intro _ r hr
        cases hr
  | cons r rs ih =>
      change allRoundConditions
          (windowToRoundRules r ++ windowsToRoundRules rs) K ↔
          allWindowConditions (r :: rs) K
      rw [allRoundConditions_append, windowToRoundRules_iff, ih]
      constructor
      · rintro ⟨hr, hrs⟩ x hx
        rcases List.mem_cons.mp hx with heq | htail
        · cases heq
          exact hr
        · exact hrs x htail
      · intro h
        constructor
        · exact h r (by simp)
        · intro x hx
          exact h x (by simp [hx])

/-- Preserve the master key while changing between window and
    round-indexed constraint witnesses. -/
def windowRoundSubtypeEquiv (rules : List WindowRule) :
    {K : Master // allWindowConditions rules K} ≃
    {K : Master // allRoundConditions (windowsToRoundRules rules) K} where
  toFun := fun ⟨K, h⟩ =>
    ⟨K, (windowsToRoundRules_correct rules K).mpr h⟩
  invFun := fun ⟨K, h⟩ =>
    ⟨K, (windowsToRoundRules_correct rules K).mp h⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

open scoped Classical in
/-- Count keys satisfying window constraints by intersecting their
    round-indexed predicates at each source slot. -/
theorem legacyWindows_card_via_rounds (rules : List WindowRule) :
    Fintype.card {K : Master // allWindowConditions rules K} =
      ∏ i : Fin 8, Fintype.card
        {w : Word // slotConditionRounds (windowsToRoundRules rules) i w} := by
  classical
  let E := (windowRoundSubtypeEquiv rules).trans
    (allRoundFiberEquiv (windowsToRoundRules rules))
  calc
    Fintype.card {K : Master // allWindowConditions rules K} =
        Fintype.card ((i : Fin 8) →
          {w : Word // slotConditionRounds (windowsToRoundRules rules) i w}) :=
      Fintype.card_congr E
    _ = _ := Fintype.card_pi

end Magma.DiffanRoundConstraints
