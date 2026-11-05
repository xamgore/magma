module

import all Init.Data.Range.Basic
public import Difan.Fibers.LabelJoinDefect

@[expose] public section

/-!
# Exactness of a coarse label when one side lies on a graph

Suppose the left window weight is supported on the graph of a
reconstruction map `point : Base → Middle`.  Instead of comparing all
pairs of middle points with the same base, we can test only right
points that differ from that reconstructed point.

This is a *conditional* test: it does not assume that the right support
lies on the same graph, and never multiplies independent DDT marginals.
-/

namespace Difan.GraphLabelExactness

variable {Middle Base : Type*}
variable [Fintype Middle] [Fintype Base]
variable [DecidableEq Middle] [DecidableEq Base]

omit [Fintype Base]

/-- The label `base` is quantitatively exact iff no active left-graph
point can be paired with a different right point having that base. -/
theorem graph_defect_zero_iff
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    LabelJoinDefect.defectMass base L R = 0 ↔
      ∀ b (m : Middle), base m = b → m ≠ point b →
        L (point b) * R m = 0 := by
  classical
  constructor
  · intro hz b m hb hne
    have hlabel : base (point b) = base m := by
      rw [hbase, hb]
    exact (LabelJoinDefect.defect_eq_zero_iff base L R).mp hz
      (point b) m hlabel (Ne.symm hne)
  · intro h
    apply (LabelJoinDefect.defect_eq_zero_iff base L R).mpr
    intro m n hlabel hne
    by_cases hp : 0 < L m
    · have hm : m = point (base m) := hleft m hp
      have hn : n ≠ point (base m) := by
        intro heq
        apply hne
        calc
          m = point (base m) := hm
          _ = n := heq.symm
      calc
        L m * R n = L (point (base m)) * R n :=
          congrArg (fun x => L x * R n) hm
        _ = 0 := h (base m) n hlabel.symm hn
    · have hz : L m = 0 := Nat.eq_zero_of_not_pos hp
      simp [hz]

/-- A graph-supported left side makes the full coarse join exact
precisely when its right off-graph contributions vanish. -/
theorem graph_coarse_eq_exact_iff
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    LabelJoinDefect.coarseMass base L R =
        LabelJoinDefect.exactMass L R ↔
      ∀ b (m : Middle), base m = b → m ≠ point b →
        L (point b) * R m = 0 := by
  classical
  have hsplit := LabelJoinDefect.coarse_eq_exact_add_defect base L R
  constructor
  · intro heq
    have hz : LabelJoinDefect.defectMass base L R = 0 := by omega
    exact (graph_defect_zero_iff base point hbase L R hleft).mp hz
  · intro h
    have hz := (graph_defect_zero_iff base point hbase L R hleft).mpr h
    rw [hsplit, hz]
    simp

/-- If a graph point and a distinct right point of the same base have
positive weights, the coarse label necessarily overcounts. -/
theorem graph_defect_pos_of_witness
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m))
    (b : Base) (m : Middle)
    (hb : base m = b) (hne : m ≠ point b)
    (hL : 0 < L (point b)) (hR : 0 < R m) :
    0 < LabelJoinDefect.defectMass base L R := by
  by_contra hn
  have hz : LabelJoinDefect.defectMass base L R = 0 :=
    Nat.eq_zero_of_not_pos hn
  have hterm := (graph_defect_zero_iff base point hbase L R hleft).mp
    hz b m hb hne
  have hpositive : 0 < L (point b) * R m := Nat.mul_pos hL hR
  omega

end Difan.GraphLabelExactness
