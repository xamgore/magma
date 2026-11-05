module

import all Init.Data.Range.Basic
public import Difan.Fibers.TwoGraphJoinMass

@[expose] public section

/-!
# Finite observations of two graph-supported windows

The full join is an equality test on reconstructed middle points.
An observation can reject mismatching points, but matching observations
need not indicate matching points. The missed mass and the rejected mass
form an exact, disjoint decomposition of the coarse count.

These results are purely finite. No DDT independence is assumed.
-/

namespace Difan.ObservedGraphJoin

variable {Base Middle Label : Type*} [Fintype Base]
variable [DecidableEq Middle] [DecidableEq Label]

/-- Join only when the two reconstructed full middle points agree. -/
def exactMass (left right : Base → Middle) (weight : Base → Nat) : Nat :=
  ∑ b : Base, if left b = right b then weight b else 0

/-- Join candidates having equal partial observations. -/
def observedMass (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat) : Nat :=
  ∑ b : Base,
    if observe (left b) = observe (right b) then weight b else 0

/-- False positives still invisible under the observation. -/
def hiddenMass (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat) : Nat :=
  ∑ b : Base,
    if observe (left b) = observe (right b) ∧ left b ≠ right b
    then weight b else 0

/-- False positives detected and excluded by the observation. -/
def rejectedMass (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat) : Nat :=
  ∑ b : Base,
    if observe (left b) ≠ observe (right b) then weight b else 0

/-- Counting all graph pairs without checking agreement. -/
def coarseMass (weight : Base → Nat) : Nat :=
  ∑ b : Base, weight b

/-- An observed match is exact up to the still-hidden mismatches. -/
theorem observed_eq_exact_add_hidden
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) :
    observedMass observe left right weight =
      exactMass left right weight + hiddenMass observe left right weight := by
  classical
  unfold observedMass exactMass hiddenMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hfull : left b = right b
  · simp [hfull]
  · by_cases hobs : observe (left b) = observe (right b)
    · simp [hfull, hobs]
    · simp [hfull, hobs]

omit [DecidableEq Middle] in
/-- Every coarse pair is either observable or already rejected. -/
theorem coarse_eq_observed_add_rejected
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) :
    coarseMass weight = observedMass observe left right weight +
      rejectedMass observe left right weight := by
  classical
  unfold coarseMass observedMass rejectedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hobs : observe (left b) = observe (right b)
  · simp [hobs]
  · simp [hobs]

/-- A three-way partition: true matches, invisible false matches,
    and visibly rejected mismatches. -/
theorem coarse_eq_exact_add_hidden_add_rejected
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) :
    coarseMass weight = exactMass left right weight +
      hiddenMass observe left right weight +
      rejectedMass observe left right weight := by
  rw [coarse_eq_observed_add_rejected observe left right weight]
  rw [observed_eq_exact_add_hidden]

/-- Exactness is equivalent to the absence of still-hidden false joins. -/
theorem observed_exact_iff_hidden_zero
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) :
    observedMass observe left right weight = exactMass left right weight ↔
      hiddenMass observe left right weight = 0 := by
  have h := observed_eq_exact_add_hidden observe left right weight
  omega

/-- A pointwise certificate sufficient for a compressed observation. -/
theorem observed_exact_of_active_agreement
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat)
    (h : ∀ b, 0 < weight b →
      observe (left b) = observe (right b) → left b = right b) :
    observedMass observe left right weight = exactMass left right weight := by
  classical
  apply (observed_exact_iff_hidden_zero observe left right weight).2
  unfold hiddenMass
  apply Finset.sum_eq_zero
  intro b _
  by_cases hpos : 0 < weight b
  · by_cases hobs : observe (left b) = observe (right b)
    · have heq := h b hpos hobs
      simp [heq]
    · simp [hobs]
  · have hz : weight b = 0 := Nat.eq_zero_of_not_pos hpos
    simp [hz]

omit [DecidableEq Middle] in
/-- Refining the observation can only reject more candidates. -/
theorem observed_mono_of_refines
    {Fine : Type*} [DecidableEq Fine]
    (coarse : Middle → Label) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (h : ∀ b, fine (left b) = fine (right b) →
      coarse (left b) = coarse (right b)) :
    observedMass fine left right weight ≤
      observedMass coarse left right weight := by
  classical
  unfold observedMass
  apply Finset.sum_le_sum
  intro b _
  by_cases hf : fine (left b) = fine (right b)
  · have hc := h b hf
    simp [hf, hc]
  · simp [hf]

end Difan.ObservedGraphJoin
