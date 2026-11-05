module

import all Init.Data.Range.Basic
public import Mathlib

@[expose] public section

/-!
# Exact joins supported on the graph of a reconstruction map

Suppose the left conditional weight can be nonzero only at points
`point b`, where `b` is the compressed observation `base m`. Then the
exact join can be indexed by `b` with no multiplicity correction.

This theorem deliberately does NOT replace the exact right weight by
its coarse marginal over all points sharing `b`. Doing so would count
false cross-joins.
-/

namespace Difan.GraphSupportedJoin

variable {Middle Base : Type*} [Fintype Middle] [Fintype Base]

/-- A left-supported graph permits an exact sum over its base coordinates.
The right weight is evaluated at the reconstructed *full* point. -/
theorem sum_eq_graph
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, L m ≠ 0 → m = point (base m)) :
    (∑ m : Middle, L m * R m) =
      ∑ b : Base, L (point b) * R (point b) := by
  classical
  symm
  apply Fintype.sum_of_injective point
      (by
        intro b c h
        have hb := congrArg base h
        simpa only [hbase] using hb)
      (fun b => L (point b) * R (point b))
      (fun m => L m * R m)
      ?_ ?_
  · intro m hm
    have hz : L m = 0 := by
      by_contra hn
      apply hm
      exact ⟨base m, (hleft m hn).symm⟩
    simp only [hz, zero_mul]
  · intro b
    rfl

/-- In particular, exact gluing along a graph is controlled by a
compressed base but retains the full-point compatibility test. -/
theorem sum_eq_graph_of_positive
    (base : Middle → Base) (point : Base → Middle)
    (hbase : ∀ b, base (point b) = b)
    (L R : Middle → Nat)
    (hleft : ∀ m, 0 < L m → m = point (base m)) :
    (∑ m : Middle, L m * R m) =
      ∑ b : Base, L (point b) * R (point b) := by
  apply sum_eq_graph base point hbase L R
  intro m hn
  exact hleft m (Nat.pos_of_ne_zero hn)

end Difan.GraphSupportedJoin
