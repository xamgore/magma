module

import all Init.Data.Range.Basic
public import Magma.Diffan.FourRoundMiddleCoordinateKernel

@[expose] public section

/-!
# Four scheduled Magma rounds: exact projection defect and diagonal midpoint

The existing four-round midpoint kernel keeps the real midpoint base
`(u,v)` and the common 256-bit master key. We now form the *smallest*
Cartesian overapproximation of the admissible midpoint pairs, by projecting
onto the two coordinates.

The difference between this rectangle's cardinality and the actual joint
count is exactly the number of missing compatible-coordinate pairs. Thus
its vanishing is equivalent to genuine rectangular separation, rather
than to a heuristic independence assumption.

A separate application restricts the concrete midpoint to `u=v` and
reduces the exact four-round count to a single 32-bit coordinate. This
works with arbitrary input/output masks and the actual key schedule.
-/

namespace Magma.DiffanFourRoundProjectionDefect

open Magma
open Magma.DiffanFourRoundScheduledMiddleFibers
open Magma.DiffanFourRoundForcedMiddleDifference
open Magma.DiffanFourRoundMiddleCoordinateKernel
open scoped Classical

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- The exact first-coordinate projection of the admissible middle fiber. -/
def rowPossible (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) (u : Word) : Prop :=
  ∃ v : Word, admissible master aL bR inputMask outputMask R u v

/-- The exact second-coordinate projection of the same middle fiber. -/
def columnPossible (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) (v : Word) : Prop :=
  ∃ u : Word, admissible master aL bR inputMask outputMask R u v

/-- The exact set of compatible midpoint base pairs. -/
noncomputable def occupied (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) : Finset (Word × Word) := by
  classical
  exact Finset.univ.filter (fun p =>
    admissible master aL bR inputMask outputMask R p.1 p.2)

/-- The minimal Cartesian rectangle containing all real compatible bases. -/
noncomputable def rectangle (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) : Finset (Word × Word) := by
  classical
  exact
    (Finset.univ.filter (rowPossible master aL bR inputMask outputMask R)).product
      (Finset.univ.filter (columnPossible master aL bR inputMask outputMask R))

/-- Pairs passing both individual projections but not jointly admissible. -/
noncomputable def missingPairs (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) : Finset (Word × Word) :=
  rectangle master aL bR inputMask outputMask R \ 
    occupied master aL bR inputMask outputMask R

private theorem occupied_mem_iff (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) (u v : Word) :
    (u, v) ∈ occupied master aL bR inputMask outputMask R ↔
      admissible master aL bR inputMask outputMask R u v := by
  classical simp [occupied]

private theorem rectangle_mem_iff (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) (u v : Word) :
    (u, v) ∈ rectangle master aL bR inputMask outputMask R ↔
      rowPossible master aL bR inputMask outputMask R u ∧
        columnPossible master aL bR inputMask outputMask R v := by
  classical simp [rectangle]

attribute [local irreducible] occupied rectangle

private theorem occupied_subset_rectangle (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) :
    occupied master aL bR inputMask outputMask R ⊆
      rectangle master aL bR inputMask outputMask R := by
  intro x hx
  rcases x with ⟨u, v⟩
  rw [occupied_mem_iff] at hx
  rw [rectangle_mem_iff]
  exact ⟨⟨v, hx⟩, ⟨u, hx⟩⟩

private theorem occupied_card (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) :
    (occupied master aL bR inputMask outputMask R).card =
      Fintype.card (baseFiber master aL bR inputMask outputMask R) := by
  classical
  symm
  exact
    Fintype.card_of_subtype (occupied master aL bR inputMask outputMask R)
      (by
        rintro ⟨u, v⟩
        exact occupied_mem_iff master aL bR inputMask outputMask R u v)

private theorem rectangle_card (master : Master) (aL bR inputMask outputMask : Word)
    (R : Point → Prop) :
    (rectangle master aL bR inputMask outputMask R).card =
      (Finset.univ.filter (rowPossible master aL bR inputMask outputMask R)).card *
        (Finset.univ.filter (columnPossible master aL bR inputMask outputMask R)).card := by
  classical
  unfold rectangle
  exact Finset.card_product _ _

/-- Main quantitative identity: the exact loss incurred by multiplying
coordinate-projection cardinalities is the number of missing midpoint base pairs. -/
theorem fourRound_exact_projection_defect (master : Master)
    (aL bR inputMask outputMask : Word) (R : Point → Prop) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) +
      (missingPairs master aL bR inputMask outputMask R).card =
    (Finset.univ.filter
      (rowPossible master aL bR inputMask outputMask R)).card *
    (Finset.univ.filter
      (columnPossible master aL bR inputMask outputMask R)).card := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card
    (occupied_subset_rectangle master aL bR inputMask outputMask R)
  calc
    _ = (occupied master aL bR inputMask outputMask R).card +
          (missingPairs master aL bR inputMask outputMask R).card := by
      rw [fourRound_exact_base_count]
      rw [occupied_card]
    _ = (missingPairs master aL bR inputMask outputMask R).card +
          (occupied master aL bR inputMask outputMask R).card :=
      Nat.add_comm _ _
    _ = (rectangle master aL bR inputMask outputMask R).card := h
    _ = _ := rectangle_card master aL bR inputMask outputMask R

/-- Vanishing projection defect means every pair of individually possible
coordinates is genuinely compatible. This is the exact converse of the
rectangle upper bound. -/
theorem missing_eq_empty_iff (master : Master)
    (aL bR inputMask outputMask : Word) (R : Point → Prop) :
    missingPairs master aL bR inputMask outputMask R = ∅ ↔
      ∀ u v : Word,
        rowPossible master aL bR inputMask outputMask R u →
        columnPossible master aL bR inputMask outputMask R v →
        admissible master aL bR inputMask outputMask R u v := by
  classical
  constructor
  · intro h u v hu hv
    by_contra hbad
    have hmem : (u, v) ∈
        missingPairs master aL bR inputMask outputMask R := by
      simp only [missingPairs, Finset.mem_sdiff]
      exact ⟨(rectangle_mem_iff master aL bR inputMask outputMask R u v).2
        ⟨hu, hv⟩,
        (occupied_mem_iff master aL bR inputMask outputMask R u v).not.mpr hbad⟩
    rw [h] at hmem
    exact Finset.notMem_empty _ hmem
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases x with ⟨u, v⟩
    have hh := (Finset.mem_sdiff.mp hx)
    have hpossible := (rectangle_mem_iff master aL bR inputMask outputMask R u v).mp hh.1
    exact hh.2 ((occupied_mem_iff master aL bR inputMask outputMask R u v).mpr
      (h u v hpossible.1 hpossible.2))

/-- A pointwise Cartesian separation certificate forces zero projection
loss. It is stronger than separate necessary conditions on the coordinates. -/
theorem missing_empty_of_separation (master : Master)
    (aL bR inputMask outputMask : Word) (R : Point → Prop)
    (P Q : Word → Prop)
    (hsep : ∀ u v,
      admissible master aL bR inputMask outputMask R u v ↔ P u ∧ Q v) :
    missingPairs master aL bR inputMask outputMask R = ∅ := by
  apply (missing_eq_empty_iff master aL bR inputMask outputMask R).2
  intro u v hu hv
  rcases hu with ⟨v₀, hu₀⟩
  rcases hv with ⟨u₀, hv₀⟩
  exact (hsep u v).2 ⟨((hsep u v₀).1 hu₀).1, ((hsep u₀ v).1 hv₀).2⟩

/-- Any actual missing cross-pair certifies strict inequality between
projected product and the exact number of four-round trajectories. -/
theorem fourRound_projection_strict_of_missing (master : Master)
    (aL bR inputMask outputMask : Word) (R : Point → Prop)
    (u v : Word)
    (hu : rowPossible master aL bR inputMask outputMask R u)
    (hv : columnPossible master aL bR inputMask outputMask R v)
    (hbad : ¬ admissible master aL bR inputMask outputMask R u v) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) R) <
    (Finset.univ.filter
      (rowPossible master aL bR inputMask outputMask R)).card *
    (Finset.univ.filter
      (columnPossible master aL bR inputMask outputMask R)).card := by
  classical
  have hmem : (u, v) ∈ missingPairs master aL bR inputMask outputMask R := by
    simp only [missingPairs, Finset.mem_sdiff]
    exact ⟨(rectangle_mem_iff master aL bR inputMask outputMask R u v).2
      ⟨hu, hv⟩,
      (occupied_mem_iff master aL bR inputMask outputMask R u v).not.mpr hbad⟩
  have hpos : 0 < (missingPairs master aL bR inputMask outputMask R).card :=
    Finset.card_pos.mpr ⟨(u, v), hmem⟩
  have heq := fourRound_exact_projection_defect master aL bR inputMask outputMask R
  omega

/-! ## A concrete, key-independent restriction on the actual midpoint -/

/-- Require the two 32-bit base words of the genuine midpoint to coincide. -/
def diagonalMiddle (mid : Point) : Prop := mid.base.1 = mid.base.2

/-- Exactly one 32-bit midpoint word remains when the actual middle base
is diagonal. No statement about independence of its two roles is made. -/
def diagonalBaseEquiv (master : Master)
    (aL bR inputMask outputMask : Word) :
    baseFiber master aL bR inputMask outputMask diagonalMiddle ≃
      {u : Word // admissible master aL bR inputMask outputMask
        diagonalMiddle u u} where
  toFun := by
    rintro ⟨⟨u, v⟩, h⟩
    have huv : u = v := h.2.1
    subst v
    exact ⟨u, h⟩
  invFun := fun w => ⟨(w.1, w.1), w.2⟩
  left_inv := by
    rintro ⟨⟨u, v⟩, h⟩
    have huv : u = v := h.2.1
    cases huv
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- Exact four-round joint count with nontrivial midpoint diagonal
constraint is a one-word count, for every scheduled master and any
input/output masks. -/
theorem fourRound_diagonal_single_word (master : Master)
    (aL bR inputMask outputMask : Word) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) inputMask)
      (outputMasked (0#32, bR) outputMask) diagonalMiddle) =
    Fintype.card {u : Word // admissible master aL bR inputMask outputMask
      diagonalMiddle u u} := by
  classical
  calc
    _ = Fintype.card (baseFiber master aL bR inputMask outputMask
      diagonalMiddle) :=
      fourRound_exact_base_count master aL bR inputMask outputMask diagonalMiddle
    _ = _ := Fintype.card_congr
      (diagonalBaseEquiv master aL bR inputMask outputMask)

end Magma.DiffanFourRoundProjectionDefect
