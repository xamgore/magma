module

import all Init.Data.Range.Basic
public import Diffan.CoordinateSeparation

@[expose] public section

/-!
# Diffan.FiberDefect — exact accounting for a failed factorization

For a finite set of candidate witnesses, `P` is the necessary condition
and `Q` is an additional coupling condition. Every candidate either
satisfies `Q` or fails `Q`, with no overlap. Consequently

  candidate count = accepted count + rejected count.

The rejected count measures the gap between the preliminary bound and
the witnesses satisfying both conditions.
-/

namespace Diffan.FiberDefect

/-- Candidate witnesses passing a preliminary condition. -/
def candidates {X : Type*} (s : Finset X) (P : X → Prop)
    [DecidablePred P] : Finset X :=
  s.filter P

/-- Candidates which also satisfy the additional condition. -/
def accepted {X : Type*} (s : Finset X)
    (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] : Finset X :=
  s.filter (fun x => P x ∧ Q x)

/-- Candidate witnesses excluded by the additional condition. -/
def rejected {X : Type*} (s : Finset X)
    (P Q : X → Prop) [DecidablePred P] [DecidablePred Q] : Finset X :=
  s.filter (fun x => P x ∧ ¬ Q x)

/-- Acceptance and rejection partition the candidate set. -/
theorem card_candidates_eq_accepted_add_rejected
    {X : Type*} [DecidableEq X]
    (s : Finset X) (P Q : X → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (candidates s P).card =
      (accepted s P Q).card + (rejected s P Q).card := by
  have hdisjoint : Disjoint (accepted s P Q) (rejected s P Q) := by
    apply Finset.disjoint_left.mpr
    intro x ha hr
    have hq : Q x := (Finset.mem_filter.mp ha).2.2
    have hnq : ¬ Q x := (Finset.mem_filter.mp hr).2.2
    exact hnq hq
  have hunion :
      accepted s P Q ∪ rejected s P Q = candidates s P := by
    ext x
    by_cases hp : P x <;> by_cases hq : Q x <;>
      simp [accepted, rejected, candidates, hp, hq]
  calc
    (candidates s P).card =
        (accepted s P Q ∪ rejected s P Q).card :=
      congrArg Finset.card hunion.symm
    _ = _ := Finset.card_union_of_disjoint hdisjoint

/-- The upper candidate count is exact precisely when every candidate
    satisfies the additional condition. -/
theorem card_accepted_eq_candidates_iff
    {X : Type*} [DecidableEq X]
    (s : Finset X) (P Q : X → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (accepted s P Q).card = (candidates s P).card ↔
      ∀ x, x ∈ s → P x → Q x := by
  have hsplit := card_candidates_eq_accepted_add_rejected s P Q
  constructor
  · intro heq x hx hp
    have hz : (rejected s P Q).card = 0 := by
      omega
    by_contra hq
    have hm : x ∈ rejected s P Q :=
      Finset.mem_filter.mpr ⟨hx, ⟨hp, hq⟩⟩
    have hempty : rejected s P Q = ∅ := Finset.card_eq_zero.mp hz
    rw [hempty] at hm
    simp at hm
  · intro hall
    have hempty : rejected s P Q = ∅ := by
      ext x
      by_cases hx : x ∈ s
      · by_cases hp : P x
        · have hq := hall x hx hp
          simp [rejected, hx, hp, hq]
        · simp [rejected, hx, hp]
      · simp [rejected, hx]
    rw [hempty] at hsplit
    simpa only [Finset.card_empty, Nat.add_zero] using hsplit.symm

end Diffan.FiberDefect
