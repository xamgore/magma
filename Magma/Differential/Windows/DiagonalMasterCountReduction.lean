module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.DiagonalMasterKeyClasses

@[expose] public section

/-!
# Reducing exact 256-bit key counts to local 32-bit classes

This file isolates the actual counting issue. Two different scheduled round
positions need not be independent parameters, but if their underlying
master-key words are DIFFERENT coordinates of a certified bijective split,
then their joint class is counted by a product, with all other 192 bits free.

The splitting equivalence is an EXPLICIT HYPOTHESIS in the quantitative
results. We prove that the two outer positions of every 3-round window
refer to distinct source slots, but do not silently assume an unproved
`BitVec 256 ≃ Word × Word × BitVec 192` compatibility with `roundKey`.
-/

namespace Magma.DifanDiagonalMasterCountReduction

open Magma
open Magma.MultiRoundDDT
open Magma.DifanDiagonalMasterKeyClasses
open Magma.DifanDiagonalSupportScheduledWindows
open Magma.OneHotFullKeyClassInvariant
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- The original source-word slot (0-based, in the order of the RFC
    baseRoundKey array), including the reversed final eight rounds. -/
def sourceSlot (r : Fin 32) : Fin 8 :=
  if r.val < 24 then
    ⟨r.val % 8, by omega⟩
  else
    ⟨7 - r.val % 8, by omega⟩

/-- The schedule selects exactly this source word from the master. -/
theorem roundKey_eq_source (K : Master) (r : Fin 32) :
    roundKey K r = baseRoundKey K (sourceSlot r) := by
  unfold roundKey sourceSlot
  dsimp only
  split_ifs <;> rfl

/-- The first and third round keys of any consecutive 3-round window
    NEVER refer to the same source word, even across the reversal at 24. -/
theorem outer_source_slots_distinct (start : Fin 30) :
    sourceSlot ⟨start.val, by omega⟩ ≠
      sourceSlot ⟨start.val + 2, by omega⟩ := by
  fin_cases start <;> decide

/-- Elementary equivalence between equal-carrier subtypes when their
    membership conditions are pointwise equivalent. -/
private def predicateEquiv {X : Type*} (P Q : X → Prop)
    (h : ∀ x, P x ↔ Q x) : {x : X // P x} ≃ {x : X // Q x} where
  toFun x := ⟨x.1, (h x.1).mp x.2⟩
  invFun x := ⟨x.1, (h x.1).mpr x.2⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

/-- An **explicit** certificate for splitting a master into the two
    relevant 32-bit round-key words and the remaining 192 bits. -/
def SplitsOuterKeys (start : Fin 30)
    (e : Master ≃ (Word × (Word × V 192))) : Prop :=
  ∀ K,
    (e K).1 = roundKey K ⟨start.val, by omega⟩ ∧
    (e K).2.1 = roundKey K ⟨start.val + 2, by omega⟩

/-- Under a certified bijection, the matching master keys are *exactly*
    a product of two constrained word fibers and an unconstrained tail. -/
private def classMasterEquiv
    (start : Fin 30) (e : Master ≃ (Word × (Word × V 192)))
    (h : SplitsOuterKeys start e) (P Q : Word → Prop) :
    {K : Master //
      P (roundKey K ⟨start.val, by omega⟩) ∧
      Q (roundKey K ⟨start.val + 2, by omega⟩)} ≃
      (({u : Word // P u} × {v : Word // Q v}) × V 192) where
  toFun := fun ⟨K, hK⟩ =>
    ((⟨(e K).1, (h K).1.symm ▸ hK.1⟩,
      ⟨(e K).2.1, (h K).2.symm ▸ hK.2⟩), (e K).2.2)
  invFun := fun p =>
    ⟨e.symm (p.1.1.1, (p.1.2.1, p.2)), by
      have he := e.apply_symm_apply (p.1.1.1, (p.1.2.1, p.2))
      have hh := h (e.symm (p.1.1.1, (p.1.2.1, p.2)))
      constructor
      · rw [← hh.1]
        simpa only [he] using p.1.1.2
      · rw [← hh.2]
        simpa only [he] using p.1.2.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv := by
    rintro ⟨⟨u, v⟩, tail⟩
    have he := e.apply_symm_apply (u.1, (v.1, tail))
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst he
      · apply Subtype.ext
        exact congrArg (fun p : Word × (Word × V 192) => p.2.1) he
    · exact congrArg (fun p : Word × (Word × V 192) => p.2.2) he

private theorem rest_card : Fintype.card (V 192) = 2 ^ 192 := by
  calc
    Fintype.card (V 192) = Fintype.card (Fin (2 ^ 192)) :=
      Fintype.card_congr (BitVec.equivFin.toEquiv)
    _ = 2 ^ 192 := Fintype.card_fin _

open scoped Classical in
/-- Main quantitative rule: two independently addressable *source words*,
    not independent artificially sampled round keys. -/
theorem count_two_local_classes_of_split
    (start : Fin 30)
    (e : Master ≃ (Word × (Word × V 192)))
    (h : SplitsOuterKeys start e)
    (P Q : Word → Prop) :
    Fintype.card {K : Master //
      P (roundKey K ⟨start.val, by omega⟩) ∧
      Q (roundKey K ⟨start.val + 2, by omega⟩)} =
      Fintype.card {u : Word // P u} *
      Fintype.card {v : Word // Q v} * 2 ^ 192 := by
  classical
  calc
    _ = Fintype.card
        (({u : Word // P u} × {v : Word // Q v}) × V 192) :=
      Fintype.card_congr (classMasterEquiv start e h P Q)
    _ = _ := by rw [Fintype.card_prod, Fintype.card_prod, rest_card]

open scoped Classical in
/-- Counts of *actual* master keys giving a positive unit-diagonal DDT,
    in terms of the already classified local parity-support sets. -/
theorem unit_diagonal_master_count_of_split
    (start : Fin 30) (aL bR : Word)
    (e : Master ≃ (Word × (Word × V 192)))
    (h : SplitsOuterKeys start e) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
        (aL, 1#32) (1#32, bR)} =
      Fintype.card {u : Word // aL ∈ parityRowSupport u} *
      Fintype.card {v : Word // bR ∈ parityRowSupport v} * 2 ^ 192 := by
  classical
  let E :
      {K : Master //
        0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
          (aL, 1#32) (1#32, bR)} ≃
      (({u : Word // aL ∈ parityRowSupport u} ×
        {v : Word // bR ∈ parityRowSupport v}) × V 192) :=
    (predicateEquiv
      (fun K : Master =>
        0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
          (aL, 1#32) (1#32, bR))
      (fun K : Master =>
        aL ∈ parityRowSupport (roundKey K ⟨start.val, by omega⟩) ∧
        bR ∈ parityRowSupport (roundKey K ⟨start.val + 2, by omega⟩))
      (fun K => scheduledThree_unit_diagonal_support_iff K start aL bR)).trans
    (classMasterEquiv start e h
      (fun u => aL ∈ parityRowSupport u)
      (fun v => bR ∈ parityRowSupport v))
  calc
    _ = Fintype.card
        (({u : Word // aL ∈ parityRowSupport u} ×
          {v : Word // bR ∈ parityRowSupport v}) × V 192) :=
      Fintype.card_congr E
    _ = _ := by rw [Fintype.card_prod, Fintype.card_prod, rest_card]

open scoped Classical in
/-- OneHot count reduced to the exact number of 32-bit words in the
    previously proved nibble/carry class. -/
theorem oneHot_diagonal_master_count_of_split
    (start : Fin 30) (j : Fin 32)
    (e : Master ≃ (Word × (Word × V 192)))
    (h : SplitsOuterKeys start e) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K start)
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32)} =
      Fintype.card {u : Word // oneHotLocalClass u j} *
      Fintype.card {v : Word // oneHotLocalClass v j} * 2 ^ 192 := by
  classical
  calc
    _ = Fintype.card {K : Master //
      oneHotLocalClass (roundKey K ⟨start.val, by omega⟩) j ∧
      oneHotLocalClass (roundKey K ⟨start.val + 2, by omega⟩) j} :=
      Fintype.card_congr (predicateEquiv _ _
        (fun K => scheduledThree_oneHot_unit_support_iff K start j))
    _ = _ := count_two_local_classes_of_split start e h
      (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)

end Magma.DifanDiagonalMasterCountReduction
