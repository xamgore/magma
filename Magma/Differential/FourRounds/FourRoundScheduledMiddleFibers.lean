module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledMeet
public import Magma.Differential.Windows.ScheduledMiddleObservation

@[expose] public section

/-!
# Four real Magma rounds: exact constrained midpoint counts

Four *ordinary* Magma G rounds are split after rounds 0 and 1.
Both two-round halves use the same 256-bit master key and its genuine
roundKey schedule. The midpoint is a full StateDifference (base + delta).

This file does not reprove the already established four-round zero-boundary
DDT product formula. Instead, it adds endpoint and midpoint predicates,
which generally destroy that Cartesian-product factorization.

The cardinality is transferred to the full intermediate fiber by a
bijection, and is then split exactly by a single observed midpoint bit.
Neither step multiplies marginal DDT values or claims that a matching
partial observation is sufficient for a real path.
-/

namespace Magma.DifanFourRoundScheduledMiddleFibers

open Magma
open Magma.DifanScheduledMeet
open scoped Classical

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

private abbrev Point :=
  Difan.StateDifference RoundState RoundState

/-- The first two rounds of the ordinary four-round prefix. -/
def firstTwo : List (Fin 32) := [0, 1]

/-- The next two ordinary rounds, using the same master. -/
def secondTwo : List (Fin 32) := [2, 3]

def left (master : Master) : Point ≃ Point :=
  leftEquiv firstTwo master

def right (master : Master) : Point ≃ Point :=
  rightEquiv secondTwo master

/-- A constraint on the real input difference and a raw input base mask. -/
def inputMasked (a : RoundState) (mask : Word) (p : Point) : Prop :=
  p.delta = a ∧ (p.base.2 &&& mask) = (0#32)

/-- A constraint on the real output difference and a raw output base mask. -/
def outputMasked (b : RoundState) (mask : Word) (p : Point) : Prop :=
  p.delta = b ∧ (p.base.1 &&& mask) = (0#32)

/-- Constraints on both the difference and the base of the actual midpoint. -/
def middleMasked (deltaMask baseMask : Word) (p : Point) : Prop :=
  (p.delta.1 &&& deltaMask) = (0#32) ∧
    (p.base.2 &&& baseMask) = (0#32)

/-- Joint four-round witnesses, including both concrete endpoints. -/
abbrev joined (master : Master) (P Q R : Point → Prop) : Type _ :=
  Difan.Meet.JoinedFiber (left master) (right master)
    (fun p => P p ∧ R (left master p)) Q

/-- The exact condition on one *complete* midpoint state/difference. -/
def middleCondition (master : Master) (P Q R : Point → Prop)
    (mid : Point) : Prop :=
  P ((left master).symm mid) ∧ R mid ∧ Q (right master mid)

/-- Count actual middle points, not independent left/right DDT marginals. -/
abbrev middleFiber (master : Master) (P Q R : Point → Prop) : Type _ :=
  {mid : Point // middleCondition master P Q R mid}

/-- Transport witnesses exactly through the invertible two-round prefix. -/
def endpointsToMiddle (master : Master) (P Q R : Point → Prop) :
    Difan.Meet.EndpointFiber (left master) (right master)
      (fun p => P p ∧ R (left master p)) Q ≃
      middleFiber master P Q R where
  toFun w :=
    ⟨left master w.1,
      ⟨by simpa only [Equiv.symm_apply_apply] using w.2.1.1,
        w.2.1.2, w.2.2⟩⟩
  invFun w :=
    ⟨(left master).symm w.1,
      ⟨⟨w.2.1, by simpa only [Equiv.apply_symm_apply] using w.2.2.1⟩,
        by simpa only [Equiv.apply_symm_apply] using w.2.2.2⟩⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (left master).symm_apply_apply w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact (left master).apply_symm_apply w.1

/-- The exact constrained four-round joint cardinality is the cardinality
of the middle *full* StateDifference fiber under one master key. -/
theorem joined_card_eq_middle_card (master : Master)
    (P Q R : Point → Prop) :
    Fintype.card (joined master P Q R) =
      Fintype.card (middleFiber master P Q R) := by
  classical
  exact Fintype.card_congr
    ((Difan.Meet.fiberEquiv (left master) (right master)
      (fun p => P p ∧ R (left master p)) Q).symm.trans
        (endpointsToMiddle master P Q R))

/-- A deliberately cheap, one-bit observation of a middle difference.
For a different mask, only this function needs to change. -/
def bitLabel (mid : Point) : Bool :=
  decide ((mid.delta.1 &&& (0x00001000#32)) ≠ (0#32))

/-- Exact middle fiber restricted to one value of the observed bit. -/
abbrev labeledFiber (master : Master) (P Q R : Point → Prop)
    (b : Bool) : Type _ :=
  {mid : Point // middleCondition master P Q R mid ∧ bitLabel mid = b}

/-- Every real middle witness belongs to one and only one bit label.
This is a partition of *actual* states, not a composition of abstract supports. -/
def middleByLabel (master : Master) (P Q R : Point → Prop) :
    middleFiber master P Q R ≃
      Σ b : Bool, labeledFiber master P Q R b where
  toFun w := ⟨bitLabel w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun w := ⟨w.2.1, w.2.2.1⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨b, ⟨mid, h, hb⟩⟩
    subst b
    rfl

/-- The observed midpoint bit partitions the constrained four-round
trajectory count into two disjoint label fibers. -/
theorem fourRound_exact_label_sum (master : Master)
    (P Q R : Point → Prop) :
    Fintype.card (joined master P Q R) =
      ∑ b : Bool, Fintype.card (labeledFiber master P Q R b) := by
  classical
  calc
    Fintype.card (joined master P Q R) =
        Fintype.card (middleFiber master P Q R) :=
      joined_card_eq_middle_card master P Q R
    _ = Fintype.card (Σ b : Bool, labeledFiber master P Q R b) :=
      Fintype.card_congr (middleByLabel master P Q R)
    _ = _ := by simp only [Fintype.card_sigma]

/-- If no full middle state occurs in either label, no valid four-round
trajectory exists. This is a certified elimination rule. -/
theorem no_fourRound_witness_of_both_labels_empty (master : Master)
    (P Q R : Point → Prop)
    (h : ∀ b : Bool, Fintype.card (labeledFiber master P Q R b) = 0) :
    Fintype.card (joined master P Q R) = 0 := by
  rw [fourRound_exact_label_sum]
  simp [h]

/-- A concrete use of nontrivial input, midpoint and output constraints.
The predicates are key-independent; only their pullback through the actual
scheduled rounds depends on the common master key. -/
theorem fourRound_masked_exact (master : Master)
    (a b : RoundState) (inputMask outputMask middleDeltaMask middleBaseMask : Word) :
    Fintype.card (joined master
      (inputMasked a inputMask) (outputMasked b outputMask)
      (middleMasked middleDeltaMask middleBaseMask)) =
    ∑ label : Bool,
      Fintype.card (labeledFiber master
        (inputMasked a inputMask) (outputMasked b outputMask)
        (middleMasked middleDeltaMask middleBaseMask) label) := by
  exact fourRound_exact_label_sum master
    (inputMasked a inputMask) (outputMasked b outputMask)
    (middleMasked middleDeltaMask middleBaseMask)

end Magma.DifanFourRoundScheduledMiddleFibers
