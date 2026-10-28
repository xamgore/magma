module

public import Magma.OneHot.Support72KeyClasses
import all Init.Data.Range.Basic

@[expose] public section

/-!
Exact cardinality of the REAL 32-bit Magma round keys with maximal
72-cell support in the single-bit-input / single-bit-output DDT matrix.

This closes the distinction between the 2016 admissible nibble tuples
and the set of actual V 32 keys.
-/

namespace Magma.OneHotSupport72ActualKeyCardinality

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotSupport72KeyClasses

private abbrev Word :=
  V 32

private abbrev Q :=
  Fin 16

private abbrev Prefix :=
  Q × Q × Q

private abbrev High :=
  Q × (Q × (Q × (Q × Q)))

private abbrev Coordinates :=
  Prefix × High

/-! ## 1. An explicit 8-digit-to-(3+5)-digit equivalence. -/

private def toCoordinates (d : Fin 8 → Q) : Coordinates :=
  ((d 0, d 1, d 2), (d 3, d 4, d 5, d 6, d 7))

private def fromCoordinates (c : Coordinates) (i : Fin 8) : Q :=
  match i.val with
  | 0 => c.1.1
  | 1 => c.1.2.1
  | 2 => c.1.2.2
  | 3 => c.2.1
  | 4 => c.2.2.1
  | 5 => c.2.2.2.1
  | 6 => c.2.2.2.2.1
  | _ => c.2.2.2.2.2

private def coordinatesEquiv : (Fin 8 → Q) ≃ Coordinates where
  toFun := toCoordinates
  invFun := fromCoordinates
  left_inv := by
    intro d
    funext i
    fin_cases i <;> rfl
  right_inv := by
    intro c
    rcases c with ⟨⟨q₀, q₁, q₂⟩, ⟨q₃, q₄, q₅, q₆, q₇⟩⟩
    rfl

/-! The existing wordDigitsEquiv has already been kernel-proved. -/

private def wordCoordinatesEquiv : Word ≃ Coordinates :=
  wordDigitsEquiv.trans coordinatesEquiv

private theorem wordCoordinatesEquiv_apply (k : Word) :
    wordCoordinatesEquiv k = toCoordinates (wordDigits k) := by rfl

/-! ## 2. Coordinate membership is precisely the proved key predicate. -/

/-- This spelling avoids referencing `maximizingHighDigits`, which was
    private to the earlier module. Both products reduce definitionally
    to the same eight-nibble set. -/
private def coordinateSet : Finset Coordinates :=
  maximizingPrefixTriples ×ˢ
    (q3Choices ×ˢ (q4Choices ×ˢ
      (q5Choices ×ˢ (q6Choices ×ˢ q7Choices))))

private theorem coordinateSet_eq_previous : coordinateSet = maximizingCoordinateTuples := by rfl

private theorem coordinates_mem_iff (d : Fin 8 → Q) :
    toCoordinates d ∈ maximizingCoordinateTuples ↔
      goodPrefix3 (d 0) (d 1) (d 2) ∧
        d 3 ∈ q3Choices ∧
        d 4 ∈ q4Choices ∧ d 5 ∈ q5Choices ∧ d 6 ∈ q6Choices ∧ d 7 ∈ q7Choices := by
  rw [← coordinateSet_eq_previous]
  simp [toCoordinates, coordinateSet, maximizingPrefixTriples]

/-! ## 3. Cardinalities of ACTUAL BitVec keys, not just nibble tuples. -/

/-- Every maximizing round key, represented as a genuine 32-bit word. -/
def max72RoundKeys : Finset Word :=
  Finset.univ.filter isMax72Key

/-- A subset of V 32 is bijective to the previously proved 2016
    admissible coordinate tuples. -/
theorem max72RoundKeys_card : max72RoundKeys.card = 2016 := by
  calc
    max72RoundKeys.card = maximizingCoordinateTuples.card := by
      refine Finset.card_equiv wordCoordinatesEquiv ?_
      intro k
      simp only [max72RoundKeys, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [wordCoordinatesEquiv_apply]
      exact (coordinates_mem_iff (wordDigits k)).symm
    _ = 2016 := maximizingCoordinateTuples_card

/-- The keys whose REAL DDT matrix has precisely 72 positive
    one-bit-to-one-bit transitions. -/
def actualMax72Keys : Finset Word :=
  Finset.univ.filter (fun k => (fastPositiveCells k).card = 72)

/-- The earlier necessary-and-sufficient theorem identifies this
    set exactly with the symbolic key-class predicate. -/
theorem actualMax72Keys_eq_max72RoundKeys :
    actualMax72Keys = max72RoundKeys := by
  ext k
  simpa only [actualMax72Keys, max72RoundKeys,
    Finset.mem_filter, Finset.mem_univ, true_and] using
      (support_eq_72_iff_key_class k)

/-- MAIN: exactly 2016 actual 32-bit round keys have the sharp
    72-transition support maximum. -/
theorem actualMax72Keys_card : actualMax72Keys.card = 2016 := by
  rw [actualMax72Keys_eq_max72RoundKeys]
  exact max72RoundKeys_card

/-- A second formulation without an auxiliary Finset name. -/
theorem actual_72_keys_filter_card :
    ((Finset.univ : Finset Word).filter
      (fun k => (fastPositiveCells k).card = 72)).card = 2016 :=
  actualMax72Keys_card

end Magma.OneHotSupport72ActualKeyCardinality
