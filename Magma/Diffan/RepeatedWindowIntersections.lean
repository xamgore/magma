module

import all Init.Data.Range.Basic
public import Magma.Diffan.OuterKeySplitCertificate

@[expose] public section

/-!
# Exact intersections for repeated three-round key windows

For each s : Fin 14 (s = 0,...,13), the two three-round windows
starting at s and s+8 lie entirely inside the first 24 ordinary
Magma rounds. Their first and third round keys refer to the SAME two
32-bit master words, respectively. The starts s=14 and s=15 must be
treated separately: their shifted windows cross the reversed-key
boundary at round 24, and the third round key ceases to repeat.

Four local conditions are therefore not independent: they reduce to
(P AND R) on the first word and (Q AND S) on the second. The previously
proved unconditional master-key count then gives an exact expression.

This is a statement about common master-key restrictions; it does not
assert statistical independence of different differential characteristics.
-/

namespace Magma.DiffanRepeatedWindowIntersections

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanDiagonalSupportScheduledWindows
open Magma.DiffanDiagonalMasterCountReduction
open Magma.DiffanOuterKeySplitCertificate
open Magma.DiffanDiagonalMasterKeyClasses

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

/-- Both windows start within the first 24 rounds, where the schedule
    repeats its eight underlying 32-bit words. The upper bound is 13,
    not 15, because the third key at s+8+2 must remain below 24. -/
def earlier (s : Fin 14) : Fin 30 := ⟨s.val, by omega⟩

def later (s : Fin 14) : Fin 30 :=
  ⟨s.val + 8, by omega⟩

/-- Two restrictions on the scheduled first/third subkeys of one window. -/
def pairCondition (start : Fin 30) (P Q : Word → Prop) (K : Master) : Prop :=
  P (roundKey K ⟨start.val, by omega⟩) ∧
  Q (roundKey K ⟨start.val + 2, by omega⟩)

/-- Joint constraints for the two windows, imposed on the SAME master. -/
def repeatedPairCondition (s : Fin 14)
    (P Q R S : Word → Prop) (K : Master) : Prop :=
  pairCondition (earlier s) P Q K ∧ pairCondition (later s) R S K

/-- The first selected master-key word repeats eight rounds later. -/
theorem repeated_first_key (K : Master) (s : Fin 14) :
    roundKey K ⟨(later s).val, by omega⟩ =
      roundKey K ⟨(earlier s).val, by omega⟩ := by
  rw [roundKey_eq_source, roundKey_eq_source]
  have hslot :
      sourceSlot ⟨(later s).val, by omega⟩ =
        sourceSlot ⟨(earlier s).val, by omega⟩ := by
    fin_cases s <;> decide
  rw [hslot]

/-- The middle word also repeats. The entire three-round key tuple
    is in fact identical in these two eight-separated windows. -/
theorem repeated_middle_key (K : Master) (s : Fin 14) :
    roundKey K ⟨(later s).val + 1, by omega⟩ =
      roundKey K ⟨(earlier s).val + 1, by omega⟩ := by
  rw [roundKey_eq_source, roundKey_eq_source]
  have hslot :
      sourceSlot ⟨(later s).val + 1, by omega⟩ =
        sourceSlot ⟨(earlier s).val + 1, by omega⟩ := by
    fin_cases s <;> decide
  rw [hslot]

/-- The third selected master-key word repeats as well. -/
theorem repeated_third_key (K : Master) (s : Fin 14) :
    roundKey K ⟨(later s).val + 2, by omega⟩ =
      roundKey K ⟨(earlier s).val + 2, by omega⟩ := by
  rw [roundKey_eq_source, roundKey_eq_source]
  have hslot :
      sourceSlot ⟨(later s).val + 2, by omega⟩ =
        sourceSlot ⟨(earlier s).val + 2, by omega⟩ := by
    fin_cases s <;> decide
  rw [hslot]

/-- The two three-round windows have exactly the same round-key tuple,
    not merely the same outer keys. Hence all their DDT coefficients agree. -/
theorem repeated_scheduledThreeKeys (K : Master) (s : Fin 14) :
    scheduledThreeKeys K (later s) =
      scheduledThreeKeys K (earlier s) := by
  funext i
  fin_cases i
  · change roundKey K ⟨(later s).val, by omega⟩ =
      roundKey K ⟨(earlier s).val, by omega⟩
    exact repeated_first_key K s
  · change roundKey K ⟨(later s).val + 1, by omega⟩ =
      roundKey K ⟨(earlier s).val + 1, by omega⟩
    exact repeated_middle_key K s
  · change roundKey K ⟨(later s).val + 2, by omega⟩ =
      roundKey K ⟨(earlier s).val + 2, by omega⟩
    exact repeated_third_key K s

/-- Eight-apart windows have the same full three-round DDT, including
    coefficients outside the middle-diagonal slice. -/
theorem repeated_threeRoundDDT (K : Master) (s : Fin 14)
    (inputDiff outputDiff : FeistelState) :
    xorDDT_rounds 3 (scheduledThreeKeys K (later s))
      inputDiff outputDiff =
    xorDDT_rounds 3 (scheduledThreeKeys K (earlier s))
      inputDiff outputDiff := by
  rw [repeated_scheduledThreeKeys]

/-- Shared scheduled words turn four conditions into two intersections.
    Notice that the conditions remain attached to one real 256-bit key. -/
theorem repeatedPairCondition_iff (s : Fin 14)
    (P Q R S : Word → Prop) (K : Master) :
    repeatedPairCondition s P Q R S K ↔
      pairCondition (earlier s)
        (fun u => P u ∧ R u) (fun v => Q v ∧ S v) K := by
  unfold repeatedPairCondition pairCondition
  rw [repeated_first_key K s, repeated_third_key K s]
  constructor
  · rintro ⟨⟨hp, hq⟩, ⟨hr, hs⟩⟩
    exact ⟨⟨hp, hr⟩, ⟨hq, hs⟩⟩
  · rintro ⟨⟨hp, hr⟩, ⟨hq, hs⟩⟩
    exact ⟨⟨hp, hq⟩, ⟨hr, hs⟩⟩

/-- Shared-word intersections describe the same constrained master keys. -/
private def repeatedSubtypeEquiv (s : Fin 14)
    (P Q R S : Word → Prop) :
    {K : Master // repeatedPairCondition s P Q R S K} ≃
      {K : Master // pairCondition (earlier s)
        (fun u => P u ∧ R u) (fun v => Q v ∧ S v) K} where
  toFun := fun ⟨K, h⟩ =>
    ⟨K, (repeatedPairCondition_iff s P Q R S K).mp h⟩
  invFun := fun ⟨K, h⟩ =>
    ⟨K, (repeatedPairCondition_iff s P Q R S K).mpr h⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

open scoped Classical in
/-- MAIN COUNT: intersections on *reused* words, not a product of four
    artificial independent round-key constraints. All other 192 bits are free. -/
theorem repeatedPairCondition_card (s : Fin 14)
    (P Q R S : Word → Prop) :
    Fintype.card {K : Master // repeatedPairCondition s P Q R S K} =
      Fintype.card {u : Word // P u ∧ R u} *
      Fintype.card {v : Word // Q v ∧ S v} * 2 ^ 192 := by
  classical
  let e := outerSplit (earlier s)
  have he : SplitsOuterKeys (earlier s) e :=
    outerSplit_correct (earlier s)
  let E :
      {K : Master // repeatedPairCondition s P Q R S K} ≃
      (({u : Word // P u ∧ R u} ×
        {v : Word // Q v ∧ S v}) × V 192) := {
    toFun := fun ⟨K, hK⟩ =>
      let hp := (repeatedPairCondition_iff s P Q R S K).mp hK
      ((⟨(e K).1, (he K).1.symm ▸ hp.1⟩,
        ⟨(e K).2.1, (he K).2.symm ▸ hp.2⟩), (e K).2.2)
    invFun := fun p =>
      ⟨e.symm (p.1.1.1, (p.1.2.1, p.2)), by
        have hround := e.apply_symm_apply (p.1.1.1, (p.1.2.1, p.2))
        have hsched := he (e.symm (p.1.1.1, (p.1.2.1, p.2)))
        have hpair :
            pairCondition (earlier s)
              (fun u => P u ∧ R u) (fun v => Q v ∧ S v)
              (e.symm (p.1.1.1, (p.1.2.1, p.2))) := by
          constructor
          · rw [← hsched.1]
            simpa only [hround] using p.1.1.2
          · rw [← hsched.2]
            simpa only [hround] using p.1.2.2
        exact (repeatedPairCondition_iff s P Q R S _).mpr hpair⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.symm_apply_apply x.1
    right_inv := by
      rintro ⟨⟨u, v⟩, tail⟩
      have hround := e.apply_symm_apply (u.1, (v.1, tail))
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst hround
        · apply Subtype.ext
          exact congrArg (fun p : Word × (Word × V 192) => p.2.1) hround
      · exact congrArg (fun p : Word × (Word × V 192) => p.2.2) hround
  }
  have hrest : Fintype.card (V 192) = 2 ^ 192 := by
    calc
      Fintype.card (V 192) = Fintype.card (Fin (2 ^ 192)) :=
        Fintype.card_congr (BitVec.equivFin.toEquiv)
      _ = 2 ^ 192 := Fintype.card_fin _
  calc
    Fintype.card {K : Master // repeatedPairCondition s P Q R S K} =
        Fintype.card
          (({u : Word // P u ∧ R u} ×
            {v : Word // Q v ∧ S v}) × V 192) :=
      Fintype.card_congr E
    _ = Fintype.card {u : Word // P u ∧ R u} *
          Fintype.card {v : Word // Q v ∧ S v} * 2 ^ 192 := by
      rw [Fintype.card_prod, Fintype.card_prod, hrest]

open scoped Classical in
/-- In particular, two OneHot diagonal-support tests eight rounds apart
    constrain the SAME two source words. The two requested input positions
    may be distinct; their local classes must be intersected. -/
theorem repeated_oneHot_joint_card (s : Fin 14) (j t : Fin 32) :
    Fintype.card {K : Master //
      0 < xorDDT_rounds 3 (scheduledThreeKeys K (earlier s))
        (1#32, BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
      0 < xorDDT_rounds 3 (scheduledThreeKeys K (later s))
        (1#32, BitVec.ofNat 32 (2 ^ t.val))
        (BitVec.ofNat 32 (2 ^ t.val), 1#32)} =
      Fintype.card {u : Word // oneHotLocalClass u j ∧ oneHotLocalClass u t} *
      Fintype.card {v : Word // oneHotLocalClass v j ∧ oneHotLocalClass v t} *
        2 ^ 192 := by
  classical
  let E :
      {K : Master //
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (earlier s))
          (1#32, BitVec.ofNat 32 (2 ^ j.val))
          (BitVec.ofNat 32 (2 ^ j.val), 1#32) ∧
        0 < xorDDT_rounds 3 (scheduledThreeKeys K (later s))
          (1#32, BitVec.ofNat 32 (2 ^ t.val))
          (BitVec.ofNat 32 (2 ^ t.val), 1#32)} ≃
      {K : Master // repeatedPairCondition s
        (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)
        (fun u => oneHotLocalClass u t) (fun v => oneHotLocalClass v t) K} := {
    toFun := fun ⟨K, h⟩ => ⟨K, ⟨
      (scheduledThree_oneHot_unit_support_iff K (earlier s) j).mp h.1,
      (scheduledThree_oneHot_unit_support_iff K (later s) t).mp h.2⟩⟩
    invFun := fun ⟨K, h⟩ => ⟨K, ⟨
      (scheduledThree_oneHot_unit_support_iff K (earlier s) j).mpr h.1,
      (scheduledThree_oneHot_unit_support_iff K (later s) t).mpr h.2⟩⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl
  }
  calc
    _ = Fintype.card {K : Master // repeatedPairCondition s
        (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)
        (fun u => oneHotLocalClass u t) (fun v => oneHotLocalClass v t) K} :=
      Fintype.card_congr E
    _ = _ := repeatedPairCondition_card s
      (fun u => oneHotLocalClass u j) (fun v => oneHotLocalClass v j)
      (fun u => oneHotLocalClass u t) (fun v => oneHotLocalClass v t)

end Magma.DiffanRepeatedWindowIntersections
