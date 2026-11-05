module

import all Init.Data.Range.Basic
public import Mathlib

@[expose] public section

/-!
# Exact joins versus joins of partially observed states

For two families of paths with conditional multiplicities `L m` and `R m`,
the exact join matches the *same* complete middle state `m`.
A coarse observation allows two different middle states to be matched if
they carry the same label. The excess consists precisely of off-diagonal
pairs of middle states; no independence assumption is involved.

All statements concern finite types and natural-number weights.
-/

namespace Diffan.LabelJoinDefect

variable {Middle Label : Type*}
variable [Fintype Middle] [DecidableEq Middle] [DecidableEq Label]

/-- True count: paths are joined only at exactly the same middle state. -/
def exactMass (L R : Middle → Nat) : Nat :=
  ∑ m : Middle, L m * R m

/-- Coarse count: both middle states need only have the same observation. -/
def coarseMass (observe : Middle → Label) (L R : Middle → Nat) : Nat :=
  ∑ m : Middle, ∑ n : Middle,
    if observe m = observe n then L m * R n else 0

/-- Extra pairs admitted by the coarse observation but not by the true join. -/
def defectMass (observe : Middle → Label) (L R : Middle → Nat) : Nat :=
  ∑ m : Middle, ∑ n : Middle,
    if observe m = observe n ∧ m ≠ n then L m * R n else 0

/-- A label overcount consists of the diagonal and *only* the off-diagonal
contributions. Both sides are finite sums of natural numbers. -/
theorem coarse_eq_exact_add_defect
    (observe : Middle → Label) (L R : Middle → Nat) :
    coarseMass observe L R =
      exactMass L R + defectMass observe L R := by
  classical
  unfold coarseMass exactMass defectMass
  calc
    (∑ m : Middle, ∑ n : Middle,
        if observe m = observe n then L m * R n else 0) =
      ∑ m : Middle, (L m * R m +
        ∑ n : Middle,
          if observe m = observe n ∧ m ≠ n then L m * R n else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      calc
        (∑ n : Middle,
            if observe m = observe n then L m * R n else 0) =
          ∑ n : Middle,
            ((if m = n then L m * R n else 0) +
              (if observe m = observe n ∧ m ≠ n then L m * R n else 0)) := by
          apply Finset.sum_congr rfl
          intro n _
          by_cases hmn : m = n
          · subst n
            simp
          · by_cases hlabel : observe m = observe n
            · simp [hmn, hlabel]
            · simp [hmn, hlabel]
        _ = (∑ n : Middle, if m = n then L m * R n else 0) +
              (∑ n : Middle,
                if observe m = observe n ∧ m ≠ n then L m * R n else 0) := by
          rw [Finset.sum_add_distrib]
        _ = L m * R m +
              (∑ n : Middle,
                if observe m = observe n ∧ m ≠ n then L m * R n else 0) := by
          rw [Fintype.sum_ite_eq]
    _ = (∑ m : Middle, L m * R m) +
          (∑ m : Middle, ∑ n : Middle,
            if observe m = observe n ∧ m ≠ n then L m * R n else 0) := by
      rw [Finset.sum_add_distrib]

/-- Zero excess is equivalent to the absence of an active cross-pair in
any observation fiber. Inactive points with zero weights are harmless. -/
theorem defect_eq_zero_iff
    (observe : Middle → Label) (L R : Middle → Nat) :
    defectMass observe L R = 0 ↔
      ∀ m n : Middle, observe m = observe n → m ≠ n → L m * R n = 0 := by
  classical
  constructor
  · intro hz m n hlabel hne
    change (∑ m : Middle, ∑ n : Middle,
      if observe m = observe n ∧ m ≠ n then L m * R n else 0) = 0 at hz
    have hrow := (Finset.sum_eq_zero_iff.mp hz) m (Finset.mem_univ m)
    have hterm := (Finset.sum_eq_zero_iff.mp hrow) n (Finset.mem_univ n)
    simpa [hlabel, hne] using hterm
  · intro h
    change (∑ m : Middle, ∑ n : Middle,
      if observe m = observe n ∧ m ≠ n then L m * R n else 0) = 0
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro n _
    by_cases hlabel : observe m = observe n
    · by_cases hne : m ≠ n
      · simpa [hlabel, hne] using h m n hlabel hne
      · simp [hne]
    · simp [hlabel]

/-- Necessary and sufficient certificate for the coarse join to be exact. -/
theorem coarse_eq_exact_iff
    (observe : Middle → Label) (L R : Middle → Nat) :
    coarseMass observe L R = exactMass L R ↔
      ∀ m n : Middle, observe m = observe n → m ≠ n → L m * R n = 0 := by
  constructor
  · intro h
    have heq := coarse_eq_exact_add_defect observe L R
    have hz : defectMass observe L R = 0 := by omega
    exact (defect_eq_zero_iff observe L R).mp hz
  · intro h
    rw [coarse_eq_exact_add_defect, (defect_eq_zero_iff observe L R).mpr h]
    simp

/-- A deliberately coarse one-label observation overcounts even for a
finite two-state toy model, where each state has unit weight. -/
theorem bool_constant_observation_overcounts :
    coarseMass (fun _ : Bool => true) (fun _ => 1) (fun _ => 1) = 4 ∧
    exactMass (fun _ : Bool => 1) (fun _ => 1) = 2 ∧
    defectMass (fun _ : Bool => true) (fun _ => 1) (fun _ => 1) = 2 := by
  decide

end Diffan.LabelJoinDefect
