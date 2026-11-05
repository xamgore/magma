module

import all Init.Data.Range.Basic
public import Difan.Fibers.TwoRegionCertifiedJoin

@[expose] public section

/-!
# Finite priority tree of certified partial observations

Each branch has a base-only region and an observation on full states.
The first matching branch is authoritative; outside every region the
original full equality test is used. Branches may overlap, because the
first matching branch wins. The observation type is shared across this
list, but each branch may choose a different observation function.

We prove exactness and a precise list of per-branch rejection masses,
plus one last fallback mass.
-/

namespace Difan.PriorityRegionTree

variable {Base Middle Label : Type*}
variable [Fintype Base] [DecidableEq Middle] [DecidableEq Label]
open Difan.ObservedGraphJoin

/-- A proposed shortcut, with its geometric region and observation. -/
structure Branch (Base Middle Label : Type*) where
  region : Base → Prop
  observe : Middle → Label

/-- First applicable branch accepts on its observation; if no branch
applies, use exact equality. Branch predicates inspect the base only. -/
def accepts (bs : List (Branch Base Middle Label))
    (b : Base) (l r : Middle) : Prop :=
  match bs with
  | [] => l = r
  | s :: rest =>
      (s.region b ∧ s.observe l = s.observe r) ∨
      (¬s.region b ∧ accepts rest b l r)

/-- Every branch carries an independent correctness certificate. -/
def Certified (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) : Prop :=
  ∀ s ∈ bs, ∀ b, s.region b →
    s.observe (left b) = s.observe (right b) → left b = right b

omit [Fintype Base] [DecidableEq Middle] [DecidableEq Label] in
/-- A priority tree is exact pointwise whenever all its branches have
valid certificates. Overlaps cannot cause double counting. -/
theorem accepts_iff_full (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) (h : Certified bs left right) (b : Base) :
    accepts bs b (left b) (right b) ↔ left b = right b := by
  induction bs with
  | nil =>
      rfl
  | cons s rest ih =>
      have hs : ∀ x, s.region x →
          s.observe (left x) = s.observe (right x) → left x = right x :=
        h s (by simp)
      have ht : Certified rest left right := by
        intro t ht x hx hobs
        exact h t (by simp [ht]) x hx hobs
      have hi := ih ht
      constructor
      · intro ha
        rcases ha with ⟨hr, ho⟩ | ⟨hr, ha⟩
        · exact hs b hr ho
        · exact hi.mp ha
      · intro heq
        by_cases hr : s.region b
        · left
          exact ⟨hr, congrArg s.observe heq⟩
        · right
          exact ⟨hr, hi.mpr heq⟩

/-- Accepted mass for the entire priority tree. -/
noncomputable def mass (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base, if accepts bs b (left b) (right b)
    then weight b else 0

/-- The rejection mass attributed to ONE branch, subject to a prefix
gate expressing that no earlier region has already claimed this base. -/
noncomputable def branchRejected (gate : Base → Prop)
    (s : Branch Base Middle Label)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if gate b ∧ s.region b ∧ s.observe (left b) ≠ s.observe (right b)
    then weight b else 0

/-- Rejections charged to the fallback, again only at unclaimed bases. -/
noncomputable def fallbackRejected (gate : Base → Prop)
    (left right : Base → Middle) (weight : Base → Nat) : Nat := by
  classical
  exact ∑ b : Base,
    if gate b ∧ left b ≠ right b then weight b else 0

/-- A list of rejection budgets: one entry per branch, then exactly one
full-comparison fallback entry. The gate prevents overlap accounting. -/
noncomputable def rejections (bs : List (Branch Base Middle Label))
    (gate : Base → Prop) (left right : Base → Middle)
    (weight : Base → Nat) : List Nat :=
  match bs with
  | [] => [fallbackRejected gate left right weight]
  | s :: rest =>
      branchRejected gate s left right weight ::
      rejections rest (fun b => gate b ∧ ¬s.region b) left right weight

open scoped Classical in
/-- The total rejection is exactly the sum of branch-attributed budgets,
including fallback. No soundness assumption is needed for the partition. -/
theorem rejections_sum_eq
    (bs : List (Branch Base Middle Label))
    (gate : Base → Prop) (left right : Base → Middle)
    (weight : Base → Nat) :
    (rejections bs gate left right weight).sum =
      ∑ b : Base,
        if gate b ∧ ¬accepts bs b (left b) (right b)
        then weight b else 0 := by
  classical
  induction bs generalizing gate with
  | nil =>
      simp only [rejections, List.sum_cons, List.sum_nil, Nat.add_zero, fallbackRejected]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : gate b ∧ left b ≠ right b
      · simp [accepts, h]
      · simp [accepts, h]
  | cons s rest ih =>
      simp only [rejections, List.sum_cons]
      rw [ih (fun b => gate b ∧ ¬s.region b)]
      unfold branchRejected
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hg : gate b
      · by_cases hr : s.region b
        · by_cases hv : s.observe (left b) = s.observe (right b)
          · simp [accepts, hg, hr, hv]
          · simp [accepts, hg, hr, hv]
        · simp [accepts, hg, hr]
      · simp [accepts, hg]

/-- Coarse mass is accepted mass plus the sum of all disjoint rejected
budgets, for any list of priority regions. -/
theorem coarse_eq_mass_add_rejections
    (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) (weight : Base → Nat) :
    coarseMass weight = mass bs left right weight +
      (rejections bs (fun _ => True) left right weight).sum := by
  classical
  rw [rejections_sum_eq]
  unfold coarseMass mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : accepts bs b (left b) (right b)
  · simp [ha]
  · simp [ha]

omit [DecidableEq Label] in
/-- All certified branches together preserve the exact full join count. -/
theorem mass_eq_exact_of_certified
    (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) (weight : Base → Nat)
    (h : Certified bs left right) :
    mass bs left right weight = exactMass left right weight := by
  classical
  unfold mass exactMass
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : accepts bs b (left b) (right b)
  · have heq := (accepts_iff_full bs left right h b).mp ha
    rw [ite_eq_left ha, ite_eq_left heq]
  · have hne : left b ≠ right b :=
      fun heq => ha ((accepts_iff_full bs left right h b).mpr heq)
    rw [ite_eq_right ha, ite_eq_right hne]

/-- The advertised exact counting identity for a verified priority tree. -/
theorem coarse_eq_exact_add_rejections
    (bs : List (Branch Base Middle Label))
    (left right : Base → Middle) (weight : Base → Nat)
    (h : Certified bs left right) :
    coarseMass weight = exactMass left right weight +
      (rejections bs (fun _ => True) left right weight).sum := by
  rw [coarse_eq_mass_add_rejections bs left right weight]
  rw [mass_eq_exact_of_certified bs left right weight h]

omit [DecidableEq Middle] in
/-- One active mismatch at a branch that no earlier branch can claim
makes its own (not an earlier) rejection budget strictly positive. -/
theorem branch_rejected_pos_of_witness
    (gate : Base → Prop) (s : Branch Base Middle Label)
    (left right : Base → Middle) (weight : Base → Nat)
    (b : Base) (hw : 0 < weight b) (hg : gate b)
    (hr : s.region b)
    (hd : s.observe (left b) ≠ s.observe (right b)) :
    0 < branchRejected gate s left right weight := by
  classical
  have hle :
      (if gate b ∧ s.region b ∧
          s.observe (left b) ≠ s.observe (right b)
       then weight b else 0) ≤ branchRejected gate s left right weight := by
    unfold branchRejected
    apply Finset.single_le_sum
      (f := fun x : Base =>
        if gate x ∧ s.region x ∧ s.observe (left x) ≠ s.observe (right x)
        then weight x else 0)
      (a := b)
    · intro x hx
      exact Nat.zero_le _
    · exact Finset.mem_univ b
  simp [hg, hr, hd] at hle
  omega

end Difan.PriorityRegionTree
