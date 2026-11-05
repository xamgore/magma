module

import all Init.Data.Range.Basic
public import Diffan.Composition.ScheduledConstraints
public import Magma.RFC8891

@[expose] public section

/-!
# Magma.ScheduledKeyConstraints

A condition on a scheduled round key becomes a predicate on the
256-bit master key. Repeated round positions therefore impose joint
conditions on the same 32-bit word.

The indexing convention is 0-based (`Fin 32`), as in Magma.roundKey.
-/

namespace Magma.ScheduledKeyConstraints

open Magma

/-- Pull a predicate on one 32-bit round key back to the 256-bit master key. -/
def atRound (r : Fin 32) (P : V 32 → Prop) : V 256 → Prop :=
  Diffan.KeyConstraint.atStep roundKey r P

/-- The round positions `i` and `i+8` use the same 32-bit word. -/
theorem atRound_repeat8 (i : Fin 8) (P : V 32 → Prop) :
    atRound ⟨i.val + 8, by omega⟩ P =
      atRound ⟨i.val, by omega⟩ P := by
  apply Diffan.KeyConstraint.atStep_eq_of_schedule_eq
  intro master
  exact roundKey_repeat8 master i

/-- Joint conditions for rounds `i` and `i+8` can be imposed at
    a single scheduled round-key value. -/
theorem intersect_repeated_rounds (i : Fin 8)
    (P Q : V 32 → Prop) :
    Diffan.KeyConstraint.intersect
      (atRound ⟨i.val, by omega⟩ P)
      (atRound ⟨i.val + 8, by omega⟩ Q) =
    atRound ⟨i.val, by omega⟩ (Diffan.KeyConstraint.intersect P Q) := by
  apply Diffan.KeyConstraint.intersect_atStep_of_schedule_eq
  intro master
  exact (roundKey_repeat8 master i).symm

/-- Repeat-distance 16 has the same master-key semantics. -/
theorem atRound_repeat16 (i : Fin 8) (P : V 32 → Prop) :
    atRound ⟨i.val + 16, by omega⟩ P =
      atRound ⟨i.val, by omega⟩ P := by
  apply Diffan.KeyConstraint.atStep_eq_of_schedule_eq
  intro master
  exact roundKey_repeat16 master i

end Magma.ScheduledKeyConstraints
