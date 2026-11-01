module

import all Init.Data.Range.Basic
public import Mathlib

@[expose] public section

/-!
# Exact XOR correlation of two finite Boolean fibers

The identity is elementary but is the correct semantic boundary for an
amortized exact counter: for a fixed pair of Boolean fibers A,B one can
precompute the entire shift histogram

    corr(h) = # {r : A r and B (r xor h)}.

Then any family of shifted intersections is a lookup into corr, not a
fresh two-coordinate join. No independence of fiber conditions is assumed.
The FWHT algorithm and its complexity are NOT proved here.
-/

namespace Diffan.XorFiberCorrelation

/-- Number of common elements of the left fiber and the shifted right
fiber over n-bit XOR words. -/
noncomputable def correlation {n : Nat}
    (left right : BitVec n → Prop) (h : BitVec n) : Nat := by
  classical
  exact ∑ r : BitVec n, if left r ∧ right (r ^^^ h) then 1 else 0

open scoped Classical in
theorem correlation_eq_card {n : Nat} (left right : BitVec n → Prop) (h : BitVec n) :
    correlation left right h =
      ((Finset.univ : Finset (BitVec n)).filter (fun r => left r ∧ right (r ^^^ h))).card := by
  classical simp only [correlation, Finset.card_filter]

open scoped Classical in
/-- Count a two-coordinate set by first grouping all first-coordinate
fibers into the XOR shift correlation. The theorem is valid for
arbitrary predicates and shift function. -/
theorem sum_shifted_fibers_as_correlations {n : Nat}
    (left right middle : BitVec n → Prop)
    (shift : BitVec n → BitVec n) :
    (∑ r : BitVec n, ∑ z : BitVec n,
      if left r ∧ middle z ∧ right (r ^^^ shift z)
        then (1 : Nat) else 0) =
      ∑ z : BitVec n,
        if middle z then correlation left right (shift z) else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hm : middle z
  · simp [hm, correlation]
  · simp [hm]

end Diffan.XorFiberCorrelation
