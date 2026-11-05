module

import all Init.Data.Range.Basic
public import Difan.Composition.MeetFiberTransport
public import Magma.Differential.Windows.ScheduledMiddleObservation
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Concrete fiber transport through scheduled Magma rounds

A coordinate change of a real input pair can always be transported through
an invertible scheduled execution.  The *induced* midpoint and output changes
may depend on the actual state and the whole master key: this does not establish a
claim that a simple XOR difference translation commutes with 4+ rounds.

This file supplies the exact joined-fiber bijection for one common master.
The missing mathematical bridge for a desired local XOR symmetry is an
additional theorem identifying the induced output map with that simple shift.
All executions here use ordinary G rounds, not the final GStar encoding.
-/

namespace Magma.DifanScheduledMeetFiberTransport

open Magma
open Magma.DifanScheduledMeet

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- Transport an input coordinate change to the real middle state. -/
def inducedMiddle («prefix» : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) : Point ≃ Point :=
  (leftEquiv «prefix» master).symm.trans (shift.trans (leftEquiv «prefix» master))

/-- Transport further through the true scheduled suffix. -/
def inducedFinal («prefix» suffix : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) : Point ≃ Point :=
  (rightEquiv suffix master).symm.trans
    ((inducedMiddle «prefix» master shift).trans (rightEquiv suffix master))

theorem inducedMiddle_comm («prefix» : List (Fin 32)) (master : Master) (shift : Point ≃ Point)
    (p : Point) :
    leftEquiv «prefix» master (shift p) =
      inducedMiddle «prefix» master shift (leftEquiv «prefix» master p) := by
  simp [inducedMiddle]

theorem inducedFinal_comm («prefix» suffix : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) (p : Point) :
    rightEquiv suffix master (inducedMiddle «prefix» master shift p) =
      inducedFinal «prefix» suffix master shift (rightEquiv suffix master p) := by
  simp [inducedFinal]

/-- Image of a predicate under a bijection, using inverse substitution. -/
def pushCondition (shift : Point ≃ Point) (P : Point → Prop) : Point → Prop :=
  fun p => P (shift.symm p)

@[simp]
theorem pushCondition_apply (shift : Point ≃ Point) (P : Point → Prop) (p : Point) :
    pushCondition shift P (shift p) ↔ P p := by simp [pushCondition]

/-- A shared-master certificate for the three actual endpoint/middle changes. -/
def scheduledCertificate
    («prefix» suffix : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) (P Q R : Point → Prop) :
    Difan.MeetFiberTransport.Certificate
      (leftEquiv «prefix» master) (leftEquiv «prefix» master)
      (rightEquiv suffix master) (rightEquiv suffix master)
      P (pushCondition shift P)
      Q (pushCondition (inducedFinal «prefix» suffix master shift) Q)
      R (pushCondition (inducedMiddle «prefix» master shift) R) where
  input := shift
  middle := inducedMiddle «prefix» master shift
  output := inducedFinal «prefix» suffix master shift
  left_comm := inducedMiddle_comm «prefix» master shift
  right_comm := inducedFinal_comm «prefix» suffix master shift
  initial_iff := fun p => pushCondition_apply shift P p
  final_iff := fun p => pushCondition_apply
    (inducedFinal «prefix» suffix master shift) Q p
  middle_iff := fun p => pushCondition_apply
    (inducedMiddle «prefix» master shift) R p

/-- The actual set of joint midpoint witnesses, retaining both endpoints. -/
abbrev joinedAt («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q R : Point → Prop) : Type _ :=
  Difan.Meet.JoinedFiber
    (leftEquiv «prefix» master) (rightEquiv suffix master)
    (fun p => P p ∧ R (leftEquiv «prefix» master p)) Q

/-- The coordinate changes identify joint witnesses with the transported
    endpoint and midpoint conditions. -/
def joinedTransportEquiv
    («prefix» suffix : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) (P Q R : Point → Prop) :
    joinedAt «prefix» suffix master P Q R ≃
      joinedAt «prefix» suffix master
        (pushCondition shift P)
        (pushCondition (inducedFinal «prefix» suffix master shift) Q)
        (pushCondition (inducedMiddle «prefix» master shift) R) :=
  (scheduledCertificate «prefix» suffix master shift P Q R).joinedEquiv

open scoped Classical in
/-- Transport preserves the number of joint witnesses for a fixed master key. -/
theorem joinedCount_transport
    («prefix» suffix : List (Fin 32)) (master : Master)
    (shift : Point ≃ Point) (P Q R : Point → Prop) :
    Fintype.card (joinedAt «prefix» suffix master P Q R) =
      Fintype.card (joinedAt «prefix» suffix master
        (pushCondition shift P)
        (pushCondition (inducedFinal «prefix» suffix master shift) Q)
        (pushCondition (inducedMiddle «prefix» master shift) R)) := by
  classical
  exact Fintype.card_congr (joinedTransportEquiv «prefix» suffix master shift P Q R)

/-- XOR translation of the left input difference fixes the base state
    and right difference, and is its own inverse. -/
def shiftInputLeftDelta (mask : Word) : Point ≃ Point where
  toFun := fun p => ⟨p.base, (p.delta.1 ^^^ mask, p.delta.2)⟩
  invFun := fun p => ⟨p.base, (p.delta.1 ^^^ mask, p.delta.2)⟩
  left_inv := by
    rintro ⟨base, ⟨aL, aR⟩⟩
    change (⟨base, ((aL ^^^ mask) ^^^ mask, aR)⟩ : Point) =
      ⟨base, (aL, aR)⟩
    have h : (aL ^^^ mask) ^^^ mask = aL := by bv_decide
    rw [h]
  right_inv := by
    rintro ⟨base, ⟨aL, aR⟩⟩
    change (⟨base, ((aL ^^^ mask) ^^^ mask, aR)⟩ : Point) =
      ⟨base, (aL, aR)⟩
    have h : (aL ^^^ mask) ^^^ mask = aL := by bv_decide
    rw [h]

open scoped Classical in
/-- The exact transported fiber count for the translation used in the
    three-round left-shift audit. The *output* predicate is transported
    through the real execution, NOT presumed to be a simple XOR mask. -/
theorem leftDelta_count_transport
    («prefix» suffix : List (Fin 32)) (master : Master)
    (P Q R : Point → Prop) :
    Fintype.card (joinedAt «prefix» suffix master P Q R) =
      Fintype.card (joinedAt «prefix» suffix master
        (pushCondition (shiftInputLeftDelta (0x00006000#32)) P)
        (pushCondition (inducedFinal «prefix» suffix master
          (shiftInputLeftDelta (0x00006000#32))) Q)
        (pushCondition (inducedMiddle «prefix» master
          (shiftInputLeftDelta (0x00006000#32))) R)) := by
  exact joinedCount_transport «prefix» suffix master
    (shiftInputLeftDelta (0x00006000#32)) P Q R

end Magma.DifanScheduledMeetFiberTransport
