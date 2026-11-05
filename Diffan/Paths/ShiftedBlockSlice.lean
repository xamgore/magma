module

import all Init.Data.Range.Basic
public import Diffan.Fibers.BlockwiseXorCorrelation

@[expose] public section

/-!
# Sum of shifted intersections from certified small-block data

This theorem is designed as an independent target for a later five-round
Magma instantiation. It explicitly binds ALL fixed parameters:
  - Z is the type of middle coordinates,
  - admissible selects middle constraints,
  - shift maps each coordinate to its required XOR shift,
  - f and g are the two actual whole-word weights,
  - pointwise proofs identify them with carry-indexed block mixtures.

-/

namespace Diffan.ShiftedBlockSlice

open Diffan.BlockwiseXorCorrelation

/-- A coupled count where every allowed middle coordinate z contributes
one XOR intersection of two full-word weighted fibers. -/
noncomputable def total {n m : Nat} {Z : Type*} [Fintype Z]
    (admissible : Z → Prop)
    (shift : Z → BitVec n × BitVec m)
    (f g : (BitVec n × BitVec m) → Nat) : Nat := by
  classical
  exact ∑ z : Z,
    if admissible z then blockCorr f g (shift z) else 0

open scoped Classical in
/-- Each full-word XOR join can be replaced by a sum of products of
small-block joins, without assuming independence and without
introducing new candidate pairs. -/
theorem total_eq_small_block_correlations
    {n m : Nat} {Z I J : Type*}
    [Fintype Z] [Fintype I] [Fintype J]
    (admissible : Z → Prop)
    (shift : Z → BitVec n × BitVec m)
    (f g : (BitVec n × BitVec m) → Nat)
    (leftLow : I → BitVec n → Nat)
    (leftHigh : I → BitVec m → Nat)
    (rightLow : J → BitVec n → Nat)
    (rightHigh : J → BitVec m → Nat)
    (hf : ∀ x, f x = mixture leftLow leftHigh x)
    (hg : ∀ x, g x = mixture rightLow rightHigh x) :
    total admissible shift f g =
      ∑ z : Z, if admissible z then
        ∑ i : I, ∑ j : J,
          wordCorr (leftLow i) (rightLow j) (shift z).1 *
            wordCorr (leftHigh i) (rightHigh j) (shift z).2
      else 0 := by
  classical
  unfold total
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : admissible z
  · simp only [hz, ite_true]
    exact blockCorr_of_certified_decompositions f g
      leftLow leftHigh rightLow rightHigh
      (shift z).1 (shift z).2 hf hg
  · simp only [hz, ite_false]

end Diffan.ShiftedBlockSlice
