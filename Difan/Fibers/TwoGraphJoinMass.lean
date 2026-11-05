module

import all Init.Data.Range.Basic
public import Difan.Fibers.GraphDefectMass

@[expose] public section

/-!
# Two graph-supported window masses

The left and right sides of a fixed-boundary reversible window join may
both be supported on graphs over the same observable base. The exact mass
then comes only from bases where the graph points coincide; the difference
between the coarse base join and the exact join comes only from bases
where they differ.

This is a purely finite statement; no cipher structure or DDT independence
is assumed.
-/

namespace Difan.TwoGraphJoinMass

variable {Middle Base : Type*} [Fintype Middle] [Fintype Base]
variable [DecidableEq Middle] [DecidableEq Base]

omit [DecidableEq Base] in
open scoped Classical in
/-- The *exact* full-point contraction is supported only where the graph
points agree. All mismatched graph points contribute zero exact mass. -/
theorem exact_eq_sum_matching_graphs
    (base : Middle → Base) (leftPoint rightPoint : Base → Middle)
    (hleftBase : ∀ b, base (leftPoint b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = leftPoint (base m))
    (hright : ∀ m, 0 < R m → m = rightPoint (base m)) :
    Difan.LabelJoinDefect.exactMass L R =
      ∑ b : Base,
        if leftPoint b = rightPoint b then
          L (leftPoint b) * R (rightPoint b)
        else 0 := by
  classical
  unfold Difan.LabelJoinDefect.exactMass
  rw [Difan.GraphSupportedJoin.sum_eq_graph_of_positive
    base leftPoint hleftBase L R hleft]
  apply Finset.sum_congr rfl
  intro b _
  by_cases heq : leftPoint b = rightPoint b
  · simp only [heq, ↓reduceIte]
  · have hz : R (leftPoint b) = 0 := by
      by_contra hn
      have hp : 0 < R (leftPoint b) := Nat.pos_of_ne_zero hn
      have := hright (leftPoint b) hp
      simp only [hleftBase] at this
      exact heq this
    simp only [heq, ↓reduceIte, hz, mul_zero]

open scoped Classical in
/-- Right off-graph mass collapses to one graph point, and is zero
exactly when the two predicted full points agree (or that right weight
vanishes). This is an equality of NATURAL counts. -/
theorem offGraphRightMass_eq_if_mismatch
    (base : Middle → Base) (leftPoint rightPoint : Base → Middle)
    (hrightBase : ∀ b, base (rightPoint b) = b)
    (R : Middle → Nat)
    (hright : ∀ m, 0 < R m → m = rightPoint (base m))
    (b : Base) :
    Difan.GraphDefectMass.offGraphRightMass base leftPoint R b =
      if leftPoint b = rightPoint b then 0 else R (rightPoint b) := by
  classical
  let test : Middle → Nat := fun n =>
    if b = base n ∧ leftPoint b ≠ n then 1 else 0
  have hs := Difan.GraphSupportedJoin.sum_eq_graph_of_positive
    base rightPoint hrightBase R test hright
  calc
    Difan.GraphDefectMass.offGraphRightMass base leftPoint R b =
        ∑ n : Middle, R n * test n := by
      unfold Difan.GraphDefectMass.offGraphRightMass
      apply Finset.sum_congr rfl
      intro n _
      dsimp [test]
      split_ifs <;> simp
    _ = ∑ c : Base, R (rightPoint c) * test (rightPoint c) := hs
    _ = if leftPoint b = rightPoint b then 0 else R (rightPoint b) := by
      simp only [test, hrightBase]
      calc
        (∑ c : Base, R (rightPoint c) *
            (if b = c ∧ leftPoint b ≠ rightPoint c then (1 : Nat) else 0)) =
            ∑ c : Base, if b = c then
              (if leftPoint b ≠ rightPoint c then R (rightPoint c) else 0)
              else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hc : b = c <;> simp [hc]
        _ = if leftPoint b ≠ rightPoint b then R (rightPoint b) else 0 := by
          simp only [Fintype.sum_ite_eq]
        _ = if leftPoint b = rightPoint b then 0 else R (rightPoint b) := by
          split_ifs <;> simp_all

open scoped Classical in
/-- Exact quantitative decomposition of a base-only label defect when
BOTH sides lie on independently reconstructed graphs. -/
theorem defect_eq_sum_mismatched_graphs
    (base : Middle → Base) (leftPoint rightPoint : Base → Middle)
    (hleftBase : ∀ b, base (leftPoint b) = b)
    (hrightBase : ∀ b, base (rightPoint b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = leftPoint (base m))
    (hright : ∀ m, 0 < R m → m = rightPoint (base m)) :
    Difan.LabelJoinDefect.defectMass base L R =
      ∑ b : Base, if leftPoint b = rightPoint b then 0
        else L (leftPoint b) * R (rightPoint b) := by
  classical
  rw [Difan.GraphDefectMass.defect_eq_sum_offGraph
    base leftPoint hleftBase L R hleft]
  apply Finset.sum_congr rfl
  intro b _
  rw [offGraphRightMass_eq_if_mismatch base leftPoint rightPoint
    hrightBase R hright b]
  split_ifs <;> simp

open scoped Classical in
/-- Coarse base join versus exact join are completely determined by
matching versus mismatching graph points. -/
theorem coarse_eq_sum_graph_products
    (base : Middle → Base) (leftPoint rightPoint : Base → Middle)
    (hleftBase : ∀ b, base (leftPoint b) = b)
    (hrightBase : ∀ b, base (rightPoint b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = leftPoint (base m))
    (hright : ∀ m, 0 < R m → m = rightPoint (base m)) :
    Difan.LabelJoinDefect.coarseMass base L R =
      ∑ b : Base, L (leftPoint b) * R (rightPoint b) := by
  classical
  rw [Difan.LabelJoinDefect.coarse_eq_exact_add_defect]
  rw [exact_eq_sum_matching_graphs base leftPoint rightPoint hleftBase L R hleft hright]
  rw [defect_eq_sum_mismatched_graphs base leftPoint rightPoint
    hleftBase hrightBase L R hleft hright]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

omit [Fintype Middle] [DecidableEq Base] in
open scoped Classical in
/-- The exact join is bounded by the coarse graph product, with equality
iff there is no positive contribution from bases with mismatched graphs.
This form needs only pointwise proofs of graph support. -/
theorem matching_mass_le_graph_mass
    (leftPoint rightPoint : Base → Middle) (L R : Middle → Nat) :
    (∑ b : Base,
      if leftPoint b = rightPoint b then
        L (leftPoint b) * R (rightPoint b) else 0) ≤
    ∑ b : Base, L (leftPoint b) * R (rightPoint b) := by
  classical
  apply Finset.sum_le_sum
  intro b hb
  split_ifs <;> omega

end Difan.TwoGraphJoinMass
