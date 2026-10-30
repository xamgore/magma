module

import all Init.Data.Range.Basic
public import Magma.Diffan.BoundaryWindowIntersections
public import Magma.Diffan.OuterKeySplitCertificate
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Exact intersections of arbitrary three-round windows

A three-round middle-diagonal constraint only inspects the first and third
round keys. For any pair of windows s,t : Fin 30, their four local
predicates must therefore be grouped by source slot rather than nominal round position.

The actual Magma master key is bijective to eight 32-bit source words
(`eightWordsEquiv`). At each source slot, collect every condition that
refers to that slot. The exact number of matching 256-bit master keys is
then a product of eight local cardinalities, even if slots repeat or the
two windows overlap in a crossed order.

An equivalence to a dependent product of local subtypes gives the count
through `Fintype.card_pi`. The earlier two-word and three-word count theorems are special
cases of this general rule.
-/

namespace Magma.DiffanArbitraryWindowIntersections

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanRepeatedWindowIntersections
open Magma.DiffanOuterKeySplitCertificate
open Magma.DiffanDiagonalMasterKeyClasses
open Magma.DiffanDiagonalSupportScheduledWindows

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- The source-word index of the first round of a three-round window. -/
def firstSlot (s : Fin 30) : Fin 8 :=
  sourceSlot ⟨s.val, by omega⟩

/-- The source-word index of the third round of a three-round window. -/
def thirdSlot (s : Fin 30) : Fin 8 :=
  sourceSlot ⟨s.val + 2, by omega⟩

/-- Four conditions on one and the same 256-bit master key. -/
def jointPairCondition (s t : Fin 30)
    (P Q R S : Word → Prop) (K : Master) : Prop :=
  pairCondition s P Q K ∧ pairCondition t R S K

/-- All restrictions that apply to ONE of the eight source words.
    Implications make repeated slots automatically combine conditions
    using conjunction. An unused slot has no restriction at all. -/
def slotCondition (s t : Fin 30)
    (P Q R S : Word → Prop) (i : Fin 8) (w : Word) : Prop :=
  (i = firstSlot s → P w) ∧
  (i = thirdSlot s → Q w) ∧
  (i = firstSlot t → R w) ∧
  (i = thirdSlot t → S w)

/-- The master-key constraints refer to EXACTLY these four coordinates
    of the eight-word view; no extra independence assumption is made. -/
private theorem joint_iff_tuple (s t : Fin 30)
    (P Q R S : Word → Prop) (K : Master) :
    jointPairCondition s t P Q R S K ↔
      (P ((eightWordsEquiv K) (firstSlot s)) ∧
       Q ((eightWordsEquiv K) (thirdSlot s)) ∧
       R ((eightWordsEquiv K) (firstSlot t)) ∧
       S ((eightWordsEquiv K) (thirdSlot t))) := by
  unfold jointPairCondition pairCondition
  simp only [roundKey_eq_source]
  exact and_assoc

/-- Four conditions on a function of eight words are equivalent to
    demanding the appropriate conjunction at every source slot. -/
private theorem tuple_iff_all_slots (s t : Fin 30)
    (P Q R S : Word → Prop) (f : Fin 8 → Word) :
    (P (f (firstSlot s)) ∧ Q (f (thirdSlot s)) ∧
     R (f (firstSlot t)) ∧ S (f (thirdSlot t))) ↔
      ∀ i : Fin 8, slotCondition s t P Q R S i (f i) := by
  constructor
  · rintro ⟨hp, hq, hr, hs⟩ i
    constructor
    · rintro rfl
      exact hp
    constructor
    · rintro rfl
      exact hq
    constructor
    · rintro rfl
      exact hr
    · rintro rfl
      exact hs
  · intro h
    exact ⟨(h (firstSlot s)).1 rfl,
      (h (thirdSlot s)).2.1 rfl,
      (h (firstSlot t)).2.2.1 rfl,
      (h (thirdSlot t)).2.2.2 rfl⟩

/-- First change of coordinates: an actual master key, with its joint
    predicate, is replaced bijectively by the eight source words. -/
private def masterToTupleEquiv (s t : Fin 30)
    (P Q R S : Word → Prop) :
    {K : Master // jointPairCondition s t P Q R S K} ≃
    {f : Fin 8 → Word //
      P (f (firstSlot s)) ∧ Q (f (thirdSlot s)) ∧
      R (f (firstSlot t)) ∧ S (f (thirdSlot t))} where
  toFun := fun ⟨K, h⟩ =>
    ⟨eightWordsEquiv K, (joint_iff_tuple s t P Q R S K).mp h⟩
  invFun := fun ⟨f, h⟩ =>
    ⟨eightWordsEquiv.symm f,
      (joint_iff_tuple s t P Q R S (eightWordsEquiv.symm f)).mpr
        (by simpa only [Equiv.apply_symm_apply] using h)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact eightWordsEquiv.symm_apply_apply x.1
  right_inv := by
    intro x
    apply Subtype.ext
    exact eightWordsEquiv.apply_symm_apply x.1

/-- Second change of coordinates: a tuple satisfying the joint predicate
    is precisely a tuple of separately constrained source words. -/
private def tupleToFiberEquiv (s t : Fin 30)
    (P Q R S : Word → Prop) :
    {f : Fin 8 → Word //
      P (f (firstSlot s)) ∧ Q (f (thirdSlot s)) ∧
      R (f (firstSlot t)) ∧ S (f (thirdSlot t))} ≃
    ((i : Fin 8) → {w : Word // slotCondition s t P Q R S i w}) where
  toFun := fun x i =>
    ⟨x.1 i, ((tuple_iff_all_slots s t P Q R S x.1).mp x.2) i⟩
  invFun := fun g =>
    ⟨(fun i => (g i).1),
      (tuple_iff_all_slots s t P Q R S (fun i => (g i).1)).mpr
        (fun i => (g i).2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro g
    funext i
    apply Subtype.ext
    rfl

/-- Constrained master keys correspond to independently constrained source words. -/
def jointMasterFiberEquiv (s t : Fin 30) (P Q R S : Word → Prop) :
    {K : Master // jointPairCondition s t P Q R S K} ≃
      ((i : Fin 8) → {w : Word // slotCondition s t P Q R S i w}) :=
  (masterToTupleEquiv s t P Q R S).trans
    (tupleToFiberEquiv s t P Q R S)

open scoped Classical in
/-- MAIN COUNT: arbitrary windows, arbitrary four local conditions,
    including 0, 1, or 2 shared slots, with crossed orientation allowed.

    Every source word is chosen independently ONCE; restrictions at the
    same source slot are intersected before counting its possible values. -/
theorem jointPairCondition_card (s t : Fin 30)
    (P Q R S : Word → Prop) :
    Fintype.card {K : Master // jointPairCondition s t P Q R S K} =
      ∏ i : Fin 8, Fintype.card
        {w : Word // slotCondition s t P Q R S i w} := by
  classical
  calc
    Fintype.card {K : Master // jointPairCondition s t P Q R S K} =
        Fintype.card
          ((i : Fin 8) → {w : Word // slotCondition s t P Q R S i w}) :=
      Fintype.card_congr (jointMasterFiberEquiv s t P Q R S)
    _ = _ := Fintype.card_pi

/-- Concrete crossed overlap: the outer source slots of windows 0
    and 29 are the SAME TWO WORDS, but in opposite order. -/
theorem crossed_outer_slots :
    firstSlot (0 : Fin 30) = thirdSlot (29 : Fin 30) ∧
    thirdSlot (0 : Fin 30) = firstSlot (29 : Fin 30) := by
  decide

/-- The crossed case forces P and S on one word, Q and R on the other.
    This is why counting collisions by position alone is insufficient. -/
theorem crossed_joint_iff (P Q R S : Word → Prop) (K : Master) :
    jointPairCondition 0 29 P Q R S K ↔
      (P (baseRoundKey K 0) ∧ S (baseRoundKey K 0)) ∧
      (Q (baseRoundKey K 2) ∧ R (baseRoundKey K 2)) := by
  change
    (P (baseRoundKey K 0) ∧ Q (baseRoundKey K 2)) ∧
      (R (baseRoundKey K 2) ∧ S (baseRoundKey K 0)) ↔
    (P (baseRoundKey K 0) ∧ S (baseRoundKey K 0)) ∧
      (Q (baseRoundKey K 2) ∧ R (baseRoundKey K 2))
  tauto

/-- Specialization: two OneHot-support tests on any pair of windows.
    This theorem is exact even if the relevant source words repeat. -/
private def oneHotToJointEquiv (s t : Fin 30) (j u : Fin 32) :
    {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K s)
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
      0 < xorDDT_rounds 3 (scheduledThreeKeys K t)
        (1#32, BitVec.ofNat 32 (2 ^ u.val))
        (BitVec.ofNat 32 (2 ^ u.val), 1#32)} ≃
    {K : Master // jointPairCondition s t
      (fun w => oneHotLocalClass w j) (fun w => oneHotLocalClass w j)
      (fun w => oneHotLocalClass w u) (fun w => oneHotLocalClass w u) K} where
  toFun := fun ⟨K, h⟩ =>
    ⟨K, ⟨(scheduledThree_oneHot_unit_support_iff K s j).mp h.1,
      (scheduledThree_oneHot_unit_support_iff K t u).mp h.2⟩⟩
  invFun := fun ⟨K, h⟩ =>
    ⟨K, ⟨(scheduledThree_oneHot_unit_support_iff K s j).mpr h.1,
      (scheduledThree_oneHot_unit_support_iff K t u).mpr h.2⟩⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

open scoped Classical in
/-- Exact master-key count of simultaneous OneHot support in ANY pair
    of three-round windows, with no case-by-case split hypothesis. -/
theorem arbitrary_oneHot_joint_card (s t : Fin 30) (j u : Fin 32) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K s)
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
      0 < xorDDT_rounds 3 (scheduledThreeKeys K t)
        (1#32, BitVec.ofNat 32 (2 ^ u.val))
        (BitVec.ofNat 32 (2 ^ u.val), 1#32)} =
      ∏ i : Fin 8, Fintype.card
        {w : Word // slotCondition s t
          (fun w => oneHotLocalClass w j) (fun w => oneHotLocalClass w j)
          (fun w => oneHotLocalClass w u) (fun w => oneHotLocalClass w u) i w} := by
  classical
  calc
    _ = Fintype.card {K : Master // jointPairCondition s t
        (fun w => oneHotLocalClass w j) (fun w => oneHotLocalClass w j)
        (fun w => oneHotLocalClass w u) (fun w => oneHotLocalClass w u) K} :=
      Fintype.card_congr (oneHotToJointEquiv s t j u)
    _ = _ := jointPairCondition_card s t
      (fun w => oneHotLocalClass w j) (fun w => oneHotLocalClass w j)
      (fun w => oneHotLocalClass w u) (fun w => oneHotLocalClass w u)

end Magma.DiffanArbitraryWindowIntersections
