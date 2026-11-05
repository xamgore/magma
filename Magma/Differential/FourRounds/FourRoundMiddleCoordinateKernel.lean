module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundForcedMiddleDifference

@[expose] public section

/-!
# Four real Magma rounds: exact two-coordinate midpoint kernel

In the zero-right-input / zero-left-output slice, the middle difference
is forced to `(aL,bR)`. The *base* of that midpoint is still a pair
`(u,v) : V 32 × V 32`.

The exact constrained count therefore has a two-coordinate Boolean kernel.
This file proves the full sum over its fibers, the precise condition for
multiplication of two marginal counts, and a sound projected-support bound.

None of these statements assumes that the constraints on `u` and `v` are
independent. The multiplicative formula explicitly requires a separating
predicate equivalence.
-/

namespace Magma.DifanFourRoundMiddleCoordinateKernel

open Magma
open Magma.DifanFourRoundScheduledMiddleFibers
open Magma.DifanFourRoundForcedMiddleDifference
open scoped Classical

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Exact membership test on the two actual midpoint base coordinates.
It retains the input, middle and output constraints under the same master. -/
def admissible (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (u v : Word) : Prop :=
  middleCondition master
    (inputMasked (aL, 0#32) inputMask)
    (outputMasked (0#32, bR) outputMask) R
    ⟨(u, v), (aL, bR)⟩

/-- The exact fiber in the second base coordinate, conditioned on `u`. -/
abbrev verticalFiber (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (u : Word) : Type :=
  {v : Word // admissible master aL bR inputMask outputMask R u v}

/-- Rewriting the 64-bit midpoint base as the dependent pair
`u` plus an actual admissible `v` loses no paths. -/
def baseByCoordinates (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) :
    baseFiber master aL bR inputMask outputMask R ≃
      Σ u : Word, verticalFiber master aL bR inputMask outputMask R u where
  toFun := fun w => ⟨w.1.1, ⟨w.1.2, w.2⟩⟩
  invFun := fun w => ⟨(w.1, w.2.1), w.2.2⟩
  left_inv := by
    rintro ⟨⟨u, v⟩, h⟩
    rfl
  right_inv := by
    rintro ⟨u, ⟨v, h⟩⟩
    rfl

/-- The four-round constrained count is exactly a sum of conditioned
32-bit fibers. Unlike a product of DDT marginals, each inner fiber
is allowed to depend on the first coordinate. -/
theorem fourRound_exact_vertical_sum (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) =
      ∑ u : Word,
        Fintype.card (verticalFiber master aL bR inputMask outputMask R u) := by
  classical
  calc
    _ = Fintype.card (baseFiber master aL bR inputMask outputMask R) :=
      fourRound_exact_base_count master aL bR inputMask outputMask R
    _ = Fintype.card
          (Σ u : Word, verticalFiber master aL bR inputMask outputMask R u) :=
      Fintype.card_congr
        (baseByCoordinates master aL bR inputMask outputMask R)
    _ = _ := by simp only [Fintype.card_sigma]

/-- A genuinely separated predicate produces a Cartesian product of
actual midpoint witness fibers. The pointwise equivalence is a required
certificate, not a consequence of arbitrary endpoint masks. -/
def separatedBaseEquiv (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (P Q : Word → Prop)
    (hsep : ∀ u v,
      admissible master aL bR inputMask outputMask R u v ↔ P u ∧ Q v) :
    baseFiber master aL bR inputMask outputMask R ≃
      {u : Word // P u} × {v : Word // Q v} where
  toFun := fun w =>
    ⟨⟨w.1.1, ((hsep _ _).mp w.2).1⟩,
      ⟨w.1.2, ((hsep _ _).mp w.2).2⟩⟩
  invFun := fun w =>
    ⟨(w.1.1, w.2.1), (hsep _ _).mpr ⟨w.1.2, w.2.2⟩⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- Exact product formula, *only when* the whole constrained midpoint
predicate has been certified to split into independent coordinates. -/
theorem fourRound_product_of_separation (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (P Q : Word → Prop)
    (hsep : ∀ u v,
      admissible master aL bR inputMask outputMask R u v ↔ P u ∧ Q v) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) =
      Fintype.card {u : Word // P u} * Fintype.card {v : Word // Q v} := by
  classical
  calc
    _ = Fintype.card (baseFiber master aL bR inputMask outputMask R) :=
      fourRound_exact_base_count master aL bR inputMask outputMask R
    _ = Fintype.card ({u : Word // P u} × {v : Word // Q v}) :=
      Fintype.card_congr
        (separatedBaseEquiv master aL bR inputMask outputMask R P Q hsep)
    _ = _ := Fintype.card_prod _ _

/-- If `P` and `Q` are merely necessary conditions, they give a sound
upper bound but not a factorization. -/
def candidateEmbedding (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (P Q : Word → Prop)
    (hnecessary : ∀ u v,
      admissible master aL bR inputMask outputMask R u v → P u ∧ Q v) :
    baseFiber master aL bR inputMask outputMask R →
      {u : Word // P u} × {v : Word // Q v} :=
  fun w =>
    ⟨⟨w.1.1, (hnecessary _ _ w.2).1⟩,
      ⟨w.1.2, (hnecessary _ _ w.2).2⟩⟩

private theorem candidateEmbedding_injective (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop) (P Q : Word → Prop)
    (hnecessary : ∀ u v, admissible master aL bR inputMask outputMask R u v → P u ∧ Q v) :
    Function.Injective (candidateEmbedding master aL bR inputMask outputMask R P Q hnecessary) := by
  intro w z heq
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p => p.1.1) heq
  · exact congrArg (fun p => p.2.1) heq

/-- Certified overapproximation by coordinate projections. This remains
valid when endpoint conditions strongly couple both actual base words. -/
theorem fourRound_projected_upper_bound (master : Master) (aL bR : Word)
    (inputMask outputMask : Word) (R : Point → Prop)
    (P Q : Word → Prop)
    (hnecessary : ∀ u v,
      admissible master aL bR inputMask outputMask R u v → P u ∧ Q v) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) ≤
      Fintype.card {u : Word // P u} * Fintype.card {v : Word // Q v} := by
  classical
  rw [fourRound_exact_base_count]
  have hcard :
      Fintype.card (baseFiber master aL bR inputMask outputMask R) ≤
        Fintype.card ({u : Word // P u} × {v : Word // Q v}) :=
    Fintype.card_le_of_injective
      (candidateEmbedding master aL bR inputMask outputMask R P Q hnecessary)
      (candidateEmbedding_injective master aL bR inputMask outputMask R
        P Q hnecessary)
  simpa only [Fintype.card_prod] using hcard

/-- Coordinate masks restrict the midpoint base words separately and
    supply necessary conditions for the projected bound. -/
def middleCoordinateMasks (maskU maskV : Word) (mid : Point) : Prop :=
  (mid.base.1 &&& maskU) = (0#32) ∧
    (mid.base.2 &&& maskV) = (0#32)

theorem fourRound_middle_masks_upper_bound (master : Master) (aL bR : Word)
    (inputMask outputMask maskU maskV : Word) :
    Fintype.card
        (joined master (inputMasked (aL, 0#32) inputMask) (outputMasked (0#32, bR) outputMask)
          (middleCoordinateMasks maskU maskV)) ≤
      Fintype.card { u : Word // (u &&& maskU) = (0#32) } *
        Fintype.card { v : Word // (v &&& maskV) = (0#32) } := by
  classical
  rw [fourRound_exact_base_count]
  have hnecessary (u v : Word)
    (h : admissible master aL bR inputMask outputMask (middleCoordinateMasks maskU maskV) u v) :
    (u &&& maskU) = (0#32) ∧ (v &&& maskV) = (0#32) := h.2.1
  calc
    _ ≤
        Fintype.card
          ({ u : Word // (u &&& maskU) = (0#32) } × { v : Word // (v &&& maskV) = (0#32) }) :=
      Fintype.card_le_of_injective
        (candidateEmbedding master aL bR inputMask outputMask (middleCoordinateMasks maskU maskV)
          (fun u => (u &&& maskU) = (0#32)) (fun v => (v &&& maskV) = (0#32)) hnecessary)
        (candidateEmbedding_injective master aL bR inputMask outputMask
          (middleCoordinateMasks maskU maskV) (fun u => (u &&& maskU) = (0#32))
          (fun v => (v &&& maskV) = (0#32)) hnecessary)
    _ = _ := Fintype.card_prod _ _

end Magma.DifanFourRoundMiddleCoordinateKernel
