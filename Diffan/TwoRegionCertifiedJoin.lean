module

import all Init.Data.Range.Basic
public import Diffan.CertifiedFastPath

@[expose] public section

/-!
# Two certified observation regions with an exact fallback

The first region has priority. The second is used only off the first;
therefore the two proposed regions need not be disjoint and no candidate
can be counted twice. Each region can have its own observation type.
The rest of the base space is checked by full equality.

All statements are pointwise sum identities for arbitrary Nat weights.
-/

namespace Diffan.TwoRegionCertifiedJoin

variable {Base Middle First Second : Type*}
variable [Fintype Base] [DecidableEq Middle]
variable [DecidableEq First] [DecidableEq Second]
open Diffan.ObservedGraphJoin

/-- Prioritized two-region candidate mass. -/
noncomputable def stagedMass (first second : Base → Prop)
    (viewFirst : Middle → First) (viewSecond : Middle → Second)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if first b then
      if viewFirst (left b) = viewFirst (right b) then weight b else 0
    else if second b then
      if viewSecond (left b) = viewSecond (right b) then weight b else 0
    else if left b = right b then weight b else 0

/-- Mass rejected by the first observation. -/
noncomputable def firstRejected (first : Base → Prop)
    (viewFirst : Middle → First)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if first b ∧ viewFirst (left b) ≠ viewFirst (right b)
    then weight b else 0

/-- The second rejection is restricted to bases not handled by first. -/
noncomputable def secondRejected (first second : Base → Prop)
    (viewSecond : Middle → Second)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if ¬ first b ∧ second b ∧
        viewSecond (left b) ≠ viewSecond (right b)
    then weight b else 0

/-- Full-equality rejections outside both fast regions. -/
noncomputable def fallbackRejected (first second : Base → Prop)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if ¬ first b ∧ ¬ second b ∧ left b ≠ right b
    then weight b else 0

/-- Independent local certificates imply global exactness of the
prioritized two-region strategy, for arbitrary conditional weights. -/
theorem staged_eq_exact_of_certificates
    (first second : Base → Prop)
    (viewFirst : Middle → First) (viewSecond : Middle → Second)
    (left right : Base → Middle) (weight : Base → Nat)
    (hfirst : ∀ b, first b →
      viewFirst (left b) = viewFirst (right b) → left b = right b)
    (hsecond : ∀ b, second b →
      viewSecond (left b) = viewSecond (right b) → left b = right b) :
    stagedMass first second viewFirst viewSecond left right weight =
      exactMass left right weight := by
  classical
  unfold stagedMass exactMass
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : first b
  · by_cases ho : viewFirst (left b) = viewFirst (right b)
    · have heq := hfirst b hf ho
      simp [hf, heq]
    · have hne : left b ≠ right b := by
        intro heq
        exact ho (congrArg viewFirst heq)
      simp [hf, ho, hne]
  · by_cases hs : second b
    · by_cases ho : viewSecond (left b) = viewSecond (right b)
      · have heq := hsecond b hs ho
        simp [hf, hs, heq]
      · have hne : left b ≠ right b := by
          intro heq
          exact ho (congrArg viewSecond heq)
        simp [hf, hs, ho, hne]
    · simp [hf, hs]

/-- Exact partition of every coarse candidate into accepted mass
and one of the three mutually exclusive rejection mechanisms.
No soundness certificate is necessary for this accounting identity. -/
theorem coarse_eq_staged_add_rejections
    (first second : Base → Prop)
    (viewFirst : Middle → First) (viewSecond : Middle → Second)
    (left right : Base → Middle) (weight : Base → Nat) :
    coarseMass weight =
      stagedMass first second viewFirst viewSecond left right weight +
      firstRejected first viewFirst left right weight +
      secondRejected first second viewSecond left right weight +
      fallbackRejected first second left right weight := by
  classical
  unfold coarseMass stagedMass firstRejected secondRejected fallbackRejected
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : first b
  · by_cases ho : viewFirst (left b) = viewFirst (right b)
    · simp [hf, ho]
    · simp [hf, ho]
  · by_cases hs : second b
    · by_cases ho : viewSecond (left b) = viewSecond (right b)
      · simp [hf, hs, ho]
      · simp [hf, hs, ho]
    · by_cases heq : left b = right b
      · simp [hf, hs, heq]
      · simp [hf, hs, heq]

omit [DecidableEq Middle] in
/-- An active candidate rejected by the second fast region guarantees
a nonzero second-stage contribution (and is not attributed to first). -/
theorem second_rejected_pos_of_witness
    (first second : Base → Prop) (viewSecond : Middle → Second)
    (left right : Base → Middle) (weight : Base → Nat)
    (b : Base) (hw : 0 < weight b)
    (hf : ¬ first b) (hs : second b)
    (hbad : viewSecond (left b) ≠ viewSecond (right b)) :
    0 < secondRejected first second viewSecond left right weight := by
  classical
  have hle :
      (if ¬first b ∧ second b ∧
          viewSecond (left b) ≠ viewSecond (right b)
        then weight b else 0) ≤
        secondRejected first second viewSecond left right weight := by
    unfold secondRejected
    apply Finset.single_le_sum
      (f := fun x : Base =>
        if ¬first x ∧ second x ∧ viewSecond (left x) ≠ viewSecond (right x)
        then weight x else 0)
      (a := b)
    · intro x hx
      exact Nat.zero_le _
    · exact Finset.mem_univ b
  simp [hf, hs, hbad] at hle
  omega

end Diffan.TwoRegionCertifiedJoin
