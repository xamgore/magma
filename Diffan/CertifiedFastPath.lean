module

import all Init.Data.Range.Basic
public import Diffan.ObservedGraphJoin

@[expose] public section

/-!
# Certified fast-path joins with an exact fallback

A partial observation is not universally sufficient to identify full
middle points. Nevertheless, a certified region of the shared base
space can safely use a cheap observation, while all other bases use an
exact equality check. The fast region is a property of the common BASE,
not of the equality of the hidden full differences.

The proof works for arbitrary finite base spaces, reconstructed graphs,
and natural-number weights (including genuinely conditional window
counts). We also separate the weights
rejected by the fast check from those rejected by the full fallback.
-/

namespace Diffan.CertifiedFastPath

variable {Base Middle Label : Type*}
variable [Fintype Base] [DecidableEq Middle] [DecidableEq Label]
open Diffan.ObservedGraphJoin

/-- Candidate mass for a local shortcut, with the full graph equality
as a fallback off the certified base region. -/
noncomputable def hybridMass (fast : Base → Prop)
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if fast b then
      if observe (left b) = observe (right b) then weight b else 0
    else
      if left b = right b then weight b else 0

/-- Mass eliminated by the cheap observation inside the fast region. -/
noncomputable def fastRejectedMass (fast : Base → Prop)
    (observe : Middle → Label) (left right : Base → Middle)
    (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if fast b ∧ observe (left b) ≠ observe (right b) then weight b else 0

/-- Mass eliminated by full comparison outside the fast region. -/
noncomputable def fallbackRejectedMass (fast : Base → Prop)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if ¬fast b ∧ left b ≠ right b then weight b else 0

/-- No compatible graph pair is lost, provided the fast observation is
separating on the selected region. No assumptions on weights are needed. -/
theorem hybrid_eq_exact_of_certificate
    (fast : Base → Prop) (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat)
    (hcert : ∀ b, fast b →
      observe (left b) = observe (right b) → left b = right b) :
    hybridMass fast observe left right weight = exactMass left right weight := by
  classical
  unfold hybridMass exactMass
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : fast b
  · by_cases ho : observe (left b) = observe (right b)
    · have heq : left b = right b := hcert b hf ho
      simp [hf, heq]
    · have hne : left b ≠ right b := by
        intro heq
        exact ho (congrArg observe heq)
      simp [hf, ho, hne]
  · simp [hf]

/-- Exact accounting of all candidates, split between cheap and full
rejection. The identity does not require the fast region to be sound. -/
theorem coarse_eq_hybrid_add_rejections
    (fast : Base → Prop) (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat) :
    coarseMass weight = hybridMass fast observe left right weight +
      fastRejectedMass fast observe left right weight +
      fallbackRejectedMass fast left right weight := by
  classical
  unfold coarseMass hybridMass fastRejectedMass fallbackRejectedMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hf : fast b
  · by_cases ho : observe (left b) = observe (right b)
    · simp [hf, ho]
    · simp [hf, ho]
  · by_cases heq : left b = right b
    · simp [hf, heq]
    · simp [hf, heq]

omit [DecidableEq Middle] in
/-- A single active rejected pair certifies a strictly positive amount
of work handled by the inexpensive test, before the full fallback. -/
theorem fast_rejected_pos_of_witness
    (fast : Base → Prop) (observe : Middle → Label)
    (left right : Base → Middle) (weight : Base → Nat)
    (b : Base) (hw : 0 < weight b) (hf : fast b)
    (hbad : observe (left b) ≠ observe (right b)) :
    0 < fastRejectedMass fast observe left right weight := by
  classical
  have hle :
      (if fast b ∧ observe (left b) ≠ observe (right b)
        then weight b else 0) ≤
        fastRejectedMass fast observe left right weight := by
    unfold fastRejectedMass
    apply Finset.single_le_sum
      (f := fun x : Base =>
        if fast x ∧ observe (left x) ≠ observe (right x) then weight x else 0)
      (a := b)
    · intro x hx
      exact Nat.zero_le _
    · exact Finset.mem_univ b
  simp [hf, hbad] at hle
  omega

end Diffan.CertifiedFastPath
