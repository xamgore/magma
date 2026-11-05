module

import all Init.Data.Range.Basic
public import Difan.Fibers.ObservedGraphJoin

@[expose] public section

/-!
# Exact gain from refining an observation of a graph join

A graph-join observation splits a candidate count into true matches
and hidden false matches. When one observation refines another, the
newly distinguished pairs account for the change in candidate count.

The gained mass is the weight of precisely those graph pairs that pass
the coarse observation and fail the refined one. All results are for
arbitrary nonnegative natural weights, hence apply to exact path counts.
-/

namespace Difan.ObservedGraphRefinement

variable {Base Middle Coarse Fine : Type*}
variable [Fintype Base] [DecidableEq Middle]
variable [DecidableEq Coarse] [DecidableEq Fine]

/-- Mass of candidate graph pairs separated by the finer observation,
    but invisible to the coarser observation. -/
def gainedMass (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat) : Nat :=
  ∑ b : Base,
    if coarse (left b) = coarse (right b) ∧
        fine (left b) ≠ fine (right b) then weight b else 0

omit [DecidableEq Middle] in
/-- Refining a label removes exactly the newly distinguished pairs. -/
theorem observed_eq_refined_add_gain
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (hrefines : ∀ b, fine (left b) = fine (right b) →
      coarse (left b) = coarse (right b)) :
    Difan.ObservedGraphJoin.observedMass coarse left right weight =
      Difan.ObservedGraphJoin.observedMass fine left right weight +
        gainedMass coarse fine left right weight := by
  classical
  unfold Difan.ObservedGraphJoin.observedMass gainedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : fine (left b) = fine (right b)
  · have hc := hrefines b hf
    simp [hf, hc]
  · by_cases hc : coarse (left b) = coarse (right b)
    · simp [hf, hc]
    · simp [hf, hc]

/-- Every newly rejected graph pair is a genuine mismatch, so the
    exact-path mass is unchanged and hidden false mass decreases by
    exactly the gained mass. -/
theorem hidden_eq_refined_add_gain
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (hrefines : ∀ b, fine (left b) = fine (right b) →
      coarse (left b) = coarse (right b)) :
    Difan.ObservedGraphJoin.hiddenMass coarse left right weight =
      Difan.ObservedGraphJoin.hiddenMass fine left right weight +
        gainedMass coarse fine left right weight := by
  have hcoarse := Difan.ObservedGraphJoin.observed_eq_exact_add_hidden
    coarse left right weight
  have hfine := Difan.ObservedGraphJoin.observed_eq_exact_add_hidden
    fine left right weight
  have hgain := observed_eq_refined_add_gain coarse fine left right weight hrefines
  omega

omit [DecidableEq Middle] in
/-- Conversely, the rejected mass increases by precisely the same
    amount as the hidden mass decreases. -/
theorem rejected_refined_eq_rejected_add_gain
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (hrefines : ∀ b, fine (left b) = fine (right b) →
      coarse (left b) = coarse (right b)) :
    Difan.ObservedGraphJoin.rejectedMass fine left right weight =
      Difan.ObservedGraphJoin.rejectedMass coarse left right weight +
        gainedMass coarse fine left right weight := by
  have hcoarse := Difan.ObservedGraphJoin.coarse_eq_observed_add_rejected
    coarse left right weight
  have hfine := Difan.ObservedGraphJoin.coarse_eq_observed_add_rejected
    fine left right weight
  have hgain := observed_eq_refined_add_gain coarse fine left right weight hrefines
  omega

omit [DecidableEq Middle] in
/-- A single active pair distinguished by the new observation certifies
    a strictly positive quantitative improvement. -/
theorem gained_pos_of_witness
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (b : Base) (hw : 0 < weight b)
    (hc : coarse (left b) = coarse (right b))
    (hf : fine (left b) ≠ fine (right b)) :
    0 < gainedMass coarse fine left right weight := by
  classical
  have hle :
      (if coarse (left b) = coarse (right b) ∧
          fine (left b) ≠ fine (right b) then weight b else 0) ≤
        gainedMass coarse fine left right weight := by
    unfold gainedMass
    apply Finset.single_le_sum
      (f := fun x : Base =>
        if coarse (left x) = coarse (right x) ∧
            fine (left x) ≠ fine (right x) then weight x else 0)
      (a := b)
    · intro x hx
      exact Nat.zero_le _
    · exact Finset.mem_univ b
  simp [hc, hf] at hle
  omega

omit [DecidableEq Middle] in
/-- In particular, the candidate count drops strictly if the refinement
    separates at least one positively weighted pair. -/
theorem refined_strict_of_witness
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (left right : Base → Middle) (weight : Base → Nat)
    (hrefines : ∀ b, fine (left b) = fine (right b) →
      coarse (left b) = coarse (right b))
    (b : Base) (hw : 0 < weight b)
    (hc : coarse (left b) = coarse (right b))
    (hf : fine (left b) ≠ fine (right b)) :
    Difan.ObservedGraphJoin.observedMass fine left right weight <
      Difan.ObservedGraphJoin.observedMass coarse left right weight := by
  have hgain := observed_eq_refined_add_gain coarse fine left right weight hrefines
  have hp := gained_pos_of_witness coarse fine left right weight b hw hc hf
  omega

end Difan.ObservedGraphRefinement
