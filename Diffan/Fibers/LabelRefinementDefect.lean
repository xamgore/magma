module

import all Init.Data.Range.Basic
public import Diffan.Fibers.LabelJoinDefect

@[expose] public section

/-!
# Refining observation labels: the exact mass of eliminated false joins

If `fine` determines `coarse`, every cross-pair visible to `fine`
is also visible to `coarse`. The difference of their overcounts is
exactly the mass of pairs separated by `fine` but not by `coarse`.
This avoids assuming that an observation is a sufficient state.
-/

namespace Diffan.LabelRefinementDefect

variable {Middle Coarse Fine : Type*}
variable [Fintype Middle] [DecidableEq Middle]
variable [DecidableEq Coarse] [DecidableEq Fine]

/-- Pairs accepted by the coarse label but rejected by the fine one. -/
def removedMass (coarse : Middle → Coarse) (fine : Middle → Fine)
    (L R : Middle → Nat) : Nat :=
  ∑ m : Middle, ∑ n : Middle,
    if coarse m = coarse n ∧ fine m ≠ fine n then L m * R n else 0

/-- Refinement partitions the coarse-label defect into surviving and removed
false joins. The proof is entirely finite-algebraic. -/
theorem defect_refinement_split
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (hfactor : ∀ m n : Middle, fine m = fine n → coarse m = coarse n)
    (L R : Middle → Nat) :
    LabelJoinDefect.defectMass coarse L R =
      LabelJoinDefect.defectMass fine L R + removedMass coarse fine L R := by
  classical
  unfold LabelJoinDefect.defectMass removedMass
  calc
    (∑ m : Middle, ∑ n : Middle,
      if coarse m = coarse n ∧ m ≠ n then L m * R n else 0) =
      ∑ m : Middle, ∑ n : Middle,
        ((if fine m = fine n ∧ m ≠ n then L m * R n else 0) +
         (if coarse m = coarse n ∧ fine m ≠ fine n then L m * R n else 0)) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      by_cases hmn : m = n
      · subst n
        simp
      · by_cases hf : fine m = fine n
        · have hc := hfactor m n hf
          simp [hmn, hf, hc]
        · by_cases hc : coarse m = coarse n
          · simp [hmn, hf, hc]
          · simp [hmn, hf, hc]
    _ = (∑ m : Middle, ∑ n : Middle,
          if fine m = fine n ∧ m ≠ n then L m * R n else 0) +
        (∑ m : Middle, ∑ n : Middle,
          if coarse m = coarse n ∧ fine m ≠ fine n then L m * R n else 0) := by
      simp only [Finset.sum_add_distrib]

/-- Refining labels never makes the false-join mass larger. -/
theorem defect_refinement_le
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (hfactor : ∀ m n : Middle, fine m = fine n → coarse m = coarse n)
    (L R : Middle → Nat) :
    LabelJoinDefect.defectMass fine L R ≤
      LabelJoinDefect.defectMass coarse L R := by
  have h := defect_refinement_split coarse fine hfactor L R
  omega

omit [DecidableEq Middle] in
/-- One active cross-pair that is distinguished by the refinement
forces a positive removed mass, without evaluating the full sum. -/
theorem removedMass_pos_of_witness
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (L R : Middle → Nat) (m n : Middle)
    (hc : coarse m = coarse n) (hf : fine m ≠ fine n)
    (hL : 0 < L m) (hR : 0 < R n) :
    0 < removedMass coarse fine L R := by
  classical
  by_contra hnot
  have hz : removedMass coarse fine L R = 0 := Nat.eq_zero_of_not_pos hnot
  unfold removedMass at hz
  have hrow := (Finset.sum_eq_zero_iff.mp hz) m (Finset.mem_univ m)
  have hterm := (Finset.sum_eq_zero_iff.mp hrow) n (Finset.mem_univ n)
  have hprod : L m * R n = 0 := by simpa [hc, hf] using hterm
  have hp : 0 < L m * R n := Nat.mul_pos hL hR
  omega

/-- A genuine active false join eliminated by the refinement gives
STRICT improvement, although the refined label need not be exact. -/
theorem defect_refinement_strict_of_witness
    (coarse : Middle → Coarse) (fine : Middle → Fine)
    (hfactor : ∀ m n : Middle, fine m = fine n → coarse m = coarse n)
    (L R : Middle → Nat) (m n : Middle)
    (hc : coarse m = coarse n) (hf : fine m ≠ fine n)
    (hL : 0 < L m) (hR : 0 < R n) :
    LabelJoinDefect.defectMass fine L R <
      LabelJoinDefect.defectMass coarse L R := by
  have hs := defect_refinement_split coarse fine hfactor L R
  have hp := removedMass_pos_of_witness coarse fine L R m n hc hf hL hR
  omega

end Diffan.LabelRefinementDefect
