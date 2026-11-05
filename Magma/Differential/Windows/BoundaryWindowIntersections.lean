module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.RepeatedWindowIntersections
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Intersections across the forward/reversed key-schedule boundary

The two pairs of 3-round windows (14,22) and (15,23) use exactly three
master-key words each. The first words coincide; the two third words do
NOT coincide. Hence their simultaneous local-key conditions are counted
by THREE local fibers and 160 free bits, not by four independent keys.

The two rearrangements of the 256-bit master key are certified bijections.
Each joint key class corresponds to three constrained words and a free
160-bit tail.
-/

namespace Magma.DiffanBoundaryWindowIntersections

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanDiagonalSupportScheduledWindows
open Magma.DiffanDiagonalMasterKeyClasses
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanRepeatedWindowIntersections

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- The only two starts whose +8 windows straddle round 24. -/
def earlierBoundary (s : Fin 2) : Fin 30 := ⟨s.val + 14, by omega⟩

def laterBoundary (s : Fin 2) : Fin 30 :=
  ⟨s.val + 22, by omega⟩

/-- The first source word is shared in both boundary window pairs. -/
theorem boundary_first_key (K : Master) (s : Fin 2) :
    roundKey K ⟨(laterBoundary s).val, by omega⟩ =
      roundKey K ⟨(earlierBoundary s).val, by omega⟩ := by
  rw [roundKey_eq_source, roundKey_eq_source]
  have hslot :
      sourceSlot ⟨(laterBoundary s).val, by omega⟩ =
        sourceSlot ⟨(earlierBoundary s).val, by omega⟩ := by
    fin_cases s <;> decide
  rw [hslot]

/-- Two independently required third words, together with the shared first
    word, occupy three distinct source slots for both boundary starts. -/
theorem boundary_three_slots (s : Fin 2) :
    sourceSlot ⟨(earlierBoundary s).val, by omega⟩ ≠
      sourceSlot ⟨(earlierBoundary s).val + 2, by omega⟩ ∧
    sourceSlot ⟨(earlierBoundary s).val, by omega⟩ ≠
      sourceSlot ⟨(laterBoundary s).val + 2, by omega⟩ ∧
    sourceSlot ⟨(earlierBoundary s).val + 2, by omega⟩ ≠
      sourceSlot ⟨(laterBoundary s).val + 2, by omega⟩ := by
  fin_cases s <;> decide

/-- Simultaneous constraints on the same master key. -/
def boundaryPairCondition (s : Fin 2)
    (P Q R S : Word → Prop) (K : Master) : Prop :=
  pairCondition (earlierBoundary s) P Q K ∧
  pairCondition (laterBoundary s) R S K

/-- Reuse of the first word merges P and R, but Q and S are conditions on
    two DIFFERENT words near the reversed-schedule boundary. -/
theorem boundaryPairCondition_iff (s : Fin 2)
    (P Q R S : Word → Prop) (K : Master) :
    boundaryPairCondition s P Q R S K ↔
      ((P (roundKey K ⟨(earlierBoundary s).val, by omega⟩) ∧
        R (roundKey K ⟨(earlierBoundary s).val, by omega⟩)) ∧
        Q (roundKey K ⟨(earlierBoundary s).val + 2, by omega⟩) ∧
        S (roundKey K ⟨(laterBoundary s).val + 2, by omega⟩)) := by
  unfold boundaryPairCondition pairCondition
  rw [boundary_first_key K s]
  constructor
  · rintro ⟨⟨hp, hq⟩, ⟨hr, hs⟩⟩
    exact ⟨⟨hp, hr⟩, hq, hs⟩
  · rintro ⟨⟨hp, hr⟩, hq, hs⟩
    exact ⟨⟨hp, hq⟩, ⟨hr, hs⟩⟩

/-- The five unconstrained 32-bit words, reassembled as 160 bits.
    The original `baseRoundKey` uses leftmost-word-first order. -/
private def tail14 (K : Master) : V 160 :=
  baseRoundKey K 1 ++ baseRoundKey K 2 ++ baseRoundKey K 3 ++
    baseRoundKey K 4 ++ baseRoundKey K 5

private def tail15 (K : Master) : V 160 :=
  baseRoundKey K 0 ++ baseRoundKey K 2 ++ baseRoundKey K 3 ++ baseRoundKey K 4 ++ baseRoundKey K 5

/-- Select slots (6,0,7), with slots (1,2,3,4,5) packed as free bits. -/
def split14 : Master ≃ Word × (Word × (Word × V 160)) where
  toFun := fun K =>
    (baseRoundKey K 6, (baseRoundKey K 0, (baseRoundKey K 7, tail14 K)))
  invFun := fun p =>
    p.2.1 ++
      BitVec.extractLsb' 128 32 p.2.2.2 ++
      BitVec.extractLsb' 96 32 p.2.2.2 ++
      BitVec.extractLsb' 64 32 p.2.2.2 ++
      BitVec.extractLsb' 32 32 p.2.2.2 ++
      BitVec.extractLsb' 0 32 p.2.2.2 ++
      p.1 ++ p.2.2.1
  left_inv := by
    intro K
    dsimp [tail14, baseRoundKey, substring]
    bv_decide
  right_inv := by
    rintro ⟨u, v, w, t⟩
    dsimp [tail14, baseRoundKey, substring]
    bv_decide

/-- Select slots (7,1,6), with slots (0,2,3,4,5) packed as free bits. -/
def split15 : Master ≃ Word × (Word × (Word × V 160)) where
  toFun := fun K =>
    (baseRoundKey K 7, (baseRoundKey K 1, (baseRoundKey K 6, tail15 K)))
  invFun := fun p =>
    BitVec.extractLsb' 128 32 p.2.2.2 ++
      p.2.1 ++
      BitVec.extractLsb' 96 32 p.2.2.2 ++
      BitVec.extractLsb' 64 32 p.2.2.2 ++
      BitVec.extractLsb' 32 32 p.2.2.2 ++
      BitVec.extractLsb' 0 32 p.2.2.2 ++
      p.2.2.1 ++ p.1
  left_inv := by
    intro K
    dsimp [tail15, baseRoundKey, substring]
    bv_decide
  right_inv := by
    rintro ⟨u, v, w, t⟩
    dsimp [tail15, baseRoundKey, substring]
    bv_decide

/-- Both configurations use exactly three selected words. -/
def boundarySplit (s : Fin 2) : Master ≃ Word × (Word × (Word × V 160)) :=
  if s.val = 0 then split14 else split15

/-- The abstract order of the split is precisely the real round-key order:
    first (shared), earlier third, later third. -/
def SplitsBoundary (s : Fin 2)
    (e : Master ≃ Word × (Word × (Word × V 160))) : Prop :=
  ∀ K,
    (e K).1 = roundKey K ⟨(earlierBoundary s).val, by omega⟩ ∧
    (e K).2.1 = roundKey K ⟨(earlierBoundary s).val + 2, by omega⟩ ∧
    (e K).2.2.1 = roundKey K ⟨(laterBoundary s).val + 2, by omega⟩

/-- The selected source slots match the scheduled subkeys in both boundary cases. -/
theorem boundarySplit_correct (s : Fin 2) :
    SplitsBoundary s (boundarySplit s) := by
  intro K
  fin_cases s
  · change (split14 K).1 = roundKey K 14 ∧
      (split14 K).2.1 = roundKey K 16 ∧
      (split14 K).2.2.1 = roundKey K 24
    rw [roundKey_eq_source, roundKey_eq_source, roundKey_eq_source]
    exact ⟨rfl, rfl, rfl⟩
  · change (split15 K).1 = roundKey K 15 ∧
      (split15 K).2.1 = roundKey K 17 ∧
      (split15 K).2.2.1 = roundKey K 25
    rw [roundKey_eq_source, roundKey_eq_source, roundKey_eq_source]
    exact ⟨rfl, rfl, rfl⟩

/-- The four conditions constrain three source words and leave a 160-bit tail free. -/
private def boundaryMasterEquiv (s : Fin 2) (P Q R S : Word → Prop) :
    {K : Master // boundaryPairCondition s P Q R S K} ≃
      ({u : Word // P u ∧ R u} ×
        ({v : Word // Q v} × ({w : Word // S w} × V 160))) := by
  let e := boundarySplit s
  have he : SplitsBoundary s e := boundarySplit_correct s
  refine {
    toFun := fun ⟨K, hK⟩ => ?_,
    invFun := fun p => ?_,
    left_inv := ?_,
    right_inv := ?_
  }
  · have hp := (boundaryPairCondition_iff s P Q R S K).mp hK
    exact (⟨(e K).1, (he K).1.symm ▸ hp.1⟩,
      (⟨(e K).2.1, (he K).2.1.symm ▸ hp.2.1⟩,
        (⟨(e K).2.2.1, (he K).2.2.symm ▸ hp.2.2⟩, (e K).2.2.2)))
  · rcases p with ⟨u, v, w, tail⟩
    let K : Master := e.symm (u.1, (v.1, (w.1, tail)))
    have hround : e K = (u.1, (v.1, (w.1, tail))) := by
      exact e.apply_symm_apply _
    have hsched := he K
    have hpair :
        (P (roundKey K ⟨(earlierBoundary s).val, by omega⟩) ∧
         R (roundKey K ⟨(earlierBoundary s).val, by omega⟩)) ∧
        Q (roundKey K ⟨(earlierBoundary s).val + 2, by omega⟩) ∧
        S (roundKey K ⟨(laterBoundary s).val + 2, by omega⟩) := by
      constructor
      · rw [← hsched.1]
        simpa only [hround] using u.2
      constructor
      · rw [← hsched.2.1]
        simpa only [hround] using v.2
      · rw [← hsched.2.2]
        simpa only [hround] using w.2
    exact ⟨K, (boundaryPairCondition_iff s P Q R S K).mpr hpair⟩
  · intro x
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  · rintro ⟨u, v, w, tail⟩
    have hround := e.apply_symm_apply (u.1, (v.1, (w.1, tail)))
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hround
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun p : Word × (Word × (Word × V 160)) => p.2.1) hround
      · apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun p : Word × (Word × (Word × V 160)) => p.2.2.1) hround
        · exact congrArg (fun p : Word × (Word × (Word × V 160)) => p.2.2.2) hround

open scoped Classical in
/-- Exact cardinality for two boundary windows: three actual independent
    source words, not four artificial round-key parameters. -/
theorem boundaryPairCondition_card (s : Fin 2) (P Q R S : Word → Prop) :
    Fintype.card {K : Master // boundaryPairCondition s P Q R S K} =
      Fintype.card {u : Word // P u ∧ R u} *
        (Fintype.card {v : Word // Q v} *
          (Fintype.card {w : Word // S w} * 2 ^ 160)) := by
  classical
  have hrest : Fintype.card (V 160) = 2 ^ 160 := by
    calc
      Fintype.card (V 160) = Fintype.card (Fin (2 ^ 160)) :=
        Fintype.card_congr (BitVec.equivFin.toEquiv)
      _ = 2 ^ 160 := Fintype.card_fin _
  calc
    Fintype.card {K : Master // boundaryPairCondition s P Q R S K} =
        Fintype.card ({u : Word // P u ∧ R u} ×
          ({v : Word // Q v} × ({w : Word // S w} × V 160))) :=
      Fintype.card_congr (boundaryMasterEquiv s P Q R S)
    _ = _ := by rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, hrest]

open scoped Classical in
/-- Application to two independently specified OneHot diagonal tests.
    On the shared first source word, both local predicates must hold;
    the two different third words carry one predicate each. -/
theorem boundary_oneHot_joint_card (s : Fin 2) (j t : Fin 32) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K (earlierBoundary s))
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
      0 < xorDDT_rounds 3 (scheduledThreeKeys K (laterBoundary s))
        (1#32, BitVec.ofNat 32 (2 ^ t.val))
        (BitVec.ofNat 32 (2 ^ t.val), 1#32)} =
      Fintype.card {u : Word // oneHotLocalClass u j ∧ oneHotLocalClass u t} *
        (Fintype.card {v : Word // oneHotLocalClass v j} *
          (Fintype.card {w : Word // oneHotLocalClass w t} * 2 ^ 160)) := by
  classical
  let E :
      {K : Master //
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (earlierBoundary s))
          (1#32, BitVec.ofNat 32 (2 ^ j.val))
          (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (laterBoundary s))
          (1#32, BitVec.ofNat 32 (2 ^ t.val))
          (BitVec.ofNat 32 (2 ^ t.val), 1#32)} ≃
      ({u : Word // oneHotLocalClass u j ∧ oneHotLocalClass u t} ×
        ({v : Word // oneHotLocalClass v j} ×
          ({w : Word // oneHotLocalClass w t} × V 160))) :=
    ( ({
      toFun := fun ⟨K, h⟩ => ⟨K, ⟨
        (scheduledThree_oneHot_unit_support_iff K (earlierBoundary s) j).mp h.1,
        (scheduledThree_oneHot_unit_support_iff K (laterBoundary s) t).mp h.2⟩⟩
      invFun := fun ⟨K, h⟩ => ⟨K, ⟨
        (scheduledThree_oneHot_unit_support_iff K (earlierBoundary s) j).mpr h.1,
        (scheduledThree_oneHot_unit_support_iff K (laterBoundary s) t).mpr h.2⟩⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    } :
      {K : Master //
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (earlierBoundary s))
          (1#32, BitVec.ofNat 32 (2 ^ j.val))
          (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (laterBoundary s))
          (1#32, BitVec.ofNat 32 (2 ^ t.val))
          (BitVec.ofNat 32 (2 ^ t.val), 1#32)} ≃
      {K : Master // boundaryPairCondition s
        (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)
        (fun u => oneHotLocalClass u t) (fun v => oneHotLocalClass v t) K})
    ).trans (boundaryMasterEquiv s
      (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)
      (fun u => oneHotLocalClass u t) (fun v => oneHotLocalClass v t))
  have hrest : Fintype.card (V 160) = 2 ^ 160 := by
    calc
      Fintype.card (V 160) = Fintype.card (Fin (2 ^ 160)) :=
        Fintype.card_congr (BitVec.equivFin.toEquiv)
      _ = 2 ^ 160 := Fintype.card_fin _
  calc
    _ = Fintype.card
        ({u : Word // oneHotLocalClass u j ∧ oneHotLocalClass u t} ×
          ({v : Word // oneHotLocalClass v j} ×
            ({w : Word // oneHotLocalClass w t} × V 160))) :=
      Fintype.card_congr E
    _ = _ := by rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, hrest]

end Magma.DiffanBoundaryWindowIntersections
