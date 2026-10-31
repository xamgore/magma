module

import all Init.Data.Range.Basic
public import Diffan.GraphLabelExactness
public import Diffan.GraphSupportedJoin

@[expose] public section

/-!
# Exact off-graph mass of a join along a graph-supported side

The left conditional weight L is supported on the graph `point b` of a
base observation. The label-join defect is not merely characterized by
its zero set: it is exactly the weighted sum of the right mass lying
*outside* that graph, one base at a time.

The result does not assume that the right support is a graph, that
cryptographic keys are independent, or that a marginal DDT product is
valid.
-/

namespace Diffan.GraphDefectMass

variable {Middle Base : Type*}
variable [Fintype Middle] [Fintype Base]
variable [DecidableEq Middle] [DecidableEq Base]

/-- Right weight at the given base whose full point is NOT the point
predicted by the left graph. It is a finite sum, not an approximation. -/
def offGraphRightMass
    (base : Middle → Base) (point : Base → Middle)
    (R : Middle → Nat) (b : Base) : Nat :=
  ∑ n : Middle,
    if b = base n ∧ point b ≠ n then R n else 0

/-- The whole label-join defect is a sum of off-graph right masses,
weighted by the one left graph point possible at each base. -/
theorem defect_eq_sum_offGraph
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    LabelJoinDefect.defectMass base L R =
      ∑ b : Base, L (point b) * offGraphRightMass base point R b := by
  classical
  calc
    LabelJoinDefect.defectMass base L R =
        ∑ m : Middle,
          L m * (∑ n : Middle,
            if base m = base n ∧ m ≠ n then R n else 0) := by
      unfold LabelJoinDefect.defectMass
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : base m = base n ∧ m ≠ n
      · simp [h]
      · simp [h]
    _ = ∑ b : Base,
          L (point b) *
            (∑ n : Middle,
              if base (point b) = base n ∧ point b ≠ n then R n else 0) := by
      exact GraphSupportedJoin.sum_eq_graph_of_positive base point
        hbase L
        (fun m => ∑ n : Middle,
          if base m = base n ∧ m ≠ n then R n else 0)
        hleft
    _ = ∑ b : Base,
          L (point b) * offGraphRightMass base point R b := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [offGraphRightMass, hbase]

/-- Error-corrected base-label counting: coarse join = exact join
plus the explicit per-base right off-graph correction. -/
theorem coarse_eq_exact_add_offGraph
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    LabelJoinDefect.coarseMass base L R =
      LabelJoinDefect.exactMass L R +
        ∑ b : Base, L (point b) * offGraphRightMass base point R b := by
  calc
    _ = LabelJoinDefect.exactMass L R +
        LabelJoinDefect.defectMass base L R :=
      LabelJoinDefect.coarse_eq_exact_add_defect base L R
    _ = _ := by
      rw [defect_eq_sum_offGraph base point hbase L R hleft]

/-- The coarse label is exact exactly when every single base contributes
zero off-graph cross-mass. This is local and can be certified basewise. -/
theorem defect_zero_iff_local
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    LabelJoinDefect.defectMass base L R = 0 ↔
      ∀ b : Base, L (point b) * offGraphRightMass base point R b = 0 := by
  classical
  rw [defect_eq_sum_offGraph base point hbase L R hleft]
  constructor
  · intro hz b
    exact (Finset.sum_eq_zero_iff.mp hz) b (Finset.mem_univ b)
  · intro hz
    apply Finset.sum_eq_zero
    intro b _
    exact hz b

/-- One local strictly positive off-graph contribution suffices to
certify a positive global defect. -/
theorem defect_pos_of_local_mass
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m))
    (b : Base)
    (hL : 0 < L (point b))
    (hR : 0 < offGraphRightMass base point R b) :
    0 < LabelJoinDefect.defectMass base L R := by
  by_contra hzero
  have hz : LabelJoinDefect.defectMass base L R = 0 := by omega
  have hterm := (defect_zero_iff_local base point hbase L R hleft).mp hz b
  exact (Nat.ne_of_gt (Nat.mul_pos hL hR)) hterm

end Diffan.GraphDefectMass
