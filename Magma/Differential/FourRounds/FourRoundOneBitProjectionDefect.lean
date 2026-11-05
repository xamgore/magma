module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundProjectionDefect

@[expose] public section

/-!
# A genuine, strictly positive four-round projection defect from one middle bit

For the real four-round scheduled Feistel chain, fix zero input and output
*differences*. Those zero differences are propagated by any deterministic
map, independently of its key; hence the concrete midpoint bases still range
freely over all pairs of words when no endpoint base masks are imposed.

Constrain only the lowest XOR bit of the two *middle base* words to agree.
Each coordinate projection is still all of `V 32`, whereas the crossed pair
(0,1) violates the joint condition. Thus the Cartesian approximation is
strictly larger for every 256-bit master key.

This is an explicit counterexample to rectangular factorization caused by
one bit of genuine middle-state coupling. The non-rectangular predicate is
imposed at the middle: this is not a claim that the Magma S-boxes themselves
produce the defect, nor a nonzero-difference cryptanalytic distinguisher.
-/

namespace Magma.DiffanFourRoundOneBitProjectionDefect

open Magma
open Magma.DiffanReverseRound
open Magma.DiffanScheduledMeet
open Magma.DiffanFourRoundScheduledMiddleFibers
open Magma.DiffanFourRoundMiddleCoordinateKernel
open Magma.DiffanFourRoundProjectionDefect

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Diffan.StateDifference RoundState RoundState

/-- Any state map transports an identically zero XOR difference to zero.
This is a statement about actual paired inputs, not about DDT marginals. -/
private theorem transport_zero (f : RoundState → RoundState) (base : RoundState) :
    (Diffan.StateDifference.transport roundXor roundXor f
      (⟨base, ((0#32), (0#32))⟩ : Point)).delta =
        ((0#32), (0#32)) := by
  change roundXor.diff (f base)
    (f (roundXor.shift base ((0#32), (0#32)))) = ((0#32), (0#32))
  have hz : roundXor.shift base ((0#32), (0#32)) = base := by
    rcases base with ⟨u, v⟩
    change (u ^^^ (0#32), v ^^^ (0#32)) = (u, v)
    simp only [BitVec.xor_zero]
  rw [hz]
  change ((f base).1 ^^^ (f base).1,
    (f base).2 ^^^ (f base).2) = ((0#32), (0#32))
  simp only [BitVec.xor_self]

/-- The actual inverse two-round prefix also preserves zero differences. -/
private theorem left_symm_zero (master : Master) (base : RoundState) :
    ((left master).symm
      (⟨base, ((0#32), (0#32))⟩ : Point)).delta =
        ((0#32), (0#32)) := by
  change (Diffan.StateDifference.transport roundXor roundXor
    (scheduledRounds master firstTwo).toEquiv.symm
    (⟨base, ((0#32), (0#32))⟩ : Point)).delta =
      ((0#32), (0#32))
  exact transport_zero _ base

/-- The actual two-round suffix preserves zero differences. -/
private theorem right_zero (master : Master) (base : RoundState) :
    (right master
      (⟨base, ((0#32), (0#32))⟩ : Point)).delta =
        ((0#32), (0#32)) := by
  change (Diffan.StateDifference.transport roundXor roundXor
    (scheduledRounds master secondTwo).toEquiv
    (⟨base, ((0#32), (0#32))⟩ : Point)).delta =
      ((0#32), (0#32))
  exact transport_zero _ base

/-- A natural one-bit compatibility condition, independent of the key:
the least significant bits of the two concrete midpoint words agree. -/
def sameLowBit (mid : Point) : Prop :=
  ((mid.base.1 ^^^ mid.base.2) &&& (1#32)) = (0#32)

/-- At zero boundary differences and with no endpoint base masks, the
*complete* four-round middle condition is precisely that single middle bit.
In particular, it is NOT the product of two unary conditions. -/
theorem admissible_zero_iff_sameLowBit (master : Master) (u v : Word) :
    admissible master (0#32) (0#32) (0#32) (0#32)
      sameLowBit u v ↔
        sameLowBit (⟨(u, v), ((0#32), (0#32))⟩ : Point) := by
  constructor
  · intro h
    exact h.2.1
  · intro h
    change
      inputMasked ((0#32), (0#32)) (0#32)
        ((left master).symm
          (⟨(u, v), ((0#32), (0#32))⟩ : Point)) ∧
      sameLowBit (⟨(u, v), ((0#32), (0#32))⟩ : Point) ∧
      outputMasked ((0#32), (0#32)) (0#32)
        (right master (⟨(u, v), ((0#32), (0#32))⟩ : Point))
    refine ⟨?_, h, ?_⟩
    · change
        ((left master).symm
          (⟨(u, v), ((0#32), (0#32))⟩ : Point)).delta =
            ((0#32), (0#32)) ∧
        (((left master).symm
          (⟨(u, v), ((0#32), (0#32))⟩ : Point)).base.2 &&&
            (0#32)) = (0#32)
      exact ⟨left_symm_zero master (u, v), by simp⟩
    · change
        (right master
          (⟨(u, v), ((0#32), (0#32))⟩ : Point)).delta =
            ((0#32), (0#32)) ∧
        ((right master
          (⟨(u, v), ((0#32), (0#32))⟩ : Point)).base.1 &&&
            (0#32)) = (0#32)
      exact ⟨right_zero master (u, v), by simp⟩

/-- Every row coordinate occurs, with the same word as the other coordinate. -/
theorem every_row_possible (master : Master) (u : Word) :
    rowPossible master (0#32) (0#32) (0#32) (0#32)
      sameLowBit u := by
  refine ⟨u, (admissible_zero_iff_sameLowBit master u u).2 ?_⟩
  simp [sameLowBit]

/-- Every column coordinate occurs as well. -/
theorem every_column_possible (master : Master) (v : Word) :
    columnPossible master (0#32) (0#32) (0#32) (0#32)
      sameLowBit v := by
  refine ⟨v, (admissible_zero_iff_sameLowBit master v v).2 ?_⟩
  simp [sameLowBit]

/-- But these individually possible coordinates cannot be crossed. -/
theorem crossed_pair_impossible (master : Master) :
    ¬ admissible master (0#32) (0#32) (0#32) (0#32)
      sameLowBit (0#32) (1#32) := by
  intro h
  have hbit := (admissible_zero_iff_sameLowBit master (0#32) (1#32)).1 h
  exact (by unfold sameLowBit; decide :
    ¬ sameLowBit
      (⟨((0#32), (1#32)), ((0#32), (0#32))⟩ : Point)) hbit

open scoped Classical

attribute [local irreducible] missingPairs

/-- The coordinate projections contain `(0,1)`, but its conflicting low
    bits exclude it from the actual midpoint set. -/
theorem crossed_pair_missing (master : Master) :
    ((0#32), (1#32)) ∈
      missingPairs master (0#32) (0#32) (0#32) (0#32)
        sameLowBit := by
  exact (missingPairs_mem_iff master
    (0#32) (0#32) (0#32) (0#32) sameLowBit
    (0#32) (1#32)).2
      ⟨every_row_possible master (0#32),
       every_column_possible master (1#32),
       crossed_pair_impossible master⟩

/-- A strictly positive projection defect for every real 256-bit key. -/
theorem positive_projection_defect (master : Master) :
    0 < (missingPairs master (0#32) (0#32) (0#32) (0#32)
      sameLowBit).card := by
  exact Finset.card_pos.mpr
    ⟨((0#32), (1#32)), crossed_pair_missing master⟩

/-- Main quantitative conclusion: separate coordinate projections strictly
overcount the true number of constrained four-round trajectories. -/
theorem fourRound_strict_one_bit_overcount (master : Master) :
    Fintype.card (joined master
      (inputMasked ((0#32), (0#32)) (0#32))
      (outputMasked ((0#32), (0#32)) (0#32)) sameLowBit) <
    (Finset.univ.filter
      (rowPossible master (0#32) (0#32) (0#32) (0#32)
        sameLowBit)).card *
    (Finset.univ.filter
      (columnPossible master (0#32) (0#32) (0#32) (0#32)
        sameLowBit)).card := by
  classical
  exact fourRound_projection_strict_of_missing master
    (0#32) (0#32) (0#32) (0#32) sameLowBit
    (0#32) (1#32)
    (every_row_possible master (0#32))
    (every_column_possible master (1#32))
    (crossed_pair_impossible master)

/-- This real midpoint predicate provably cannot split into independent
unary predicates on the two middle coordinates. -/
theorem no_rectangular_separation (master : Master) :
    ¬ ∃ P Q : Word → Prop,
      ∀ u v : Word,
        admissible master (0#32) (0#32) (0#32) (0#32)
          sameLowBit u v ↔ P u ∧ Q v := by
  rintro ⟨P, Q, hsep⟩
  have hz := missing_empty_of_separation master
    (0#32) (0#32) (0#32) (0#32) sameLowBit P Q hsep
  have hpos := positive_projection_defect master
  rw [hz] at hpos
  simp at hpos

end Magma.DiffanFourRoundOneBitProjectionDefect
