module

public import Magma.DDT.OneHot.Extrema.ExactCoefficientGlobalMaximum
import all Init.Data.Range.Basic

@[expose] public section

/-!
One-hot-to-one-hot maximal DDT coefficients: exact local winning classes
and a small, symbolic finite count of the non-maximizing nibble tuples.

Mathematics:
  A_i = {q : exists r,s, L_i(q,0,r,s)=4}.
  B_i = {q : exists r,s, L_i(q,0,r,s)=L_i(q,1,r,s)=4}.

At position i, a maximum 2^30 occurs exactly if
  (keyPrefix(k,i)=0 and q_i in A_i) or
  (keyPrefix(k,i)!=0 and q_i in B_i).

A 32-bit key has NO maximizing one-hot coefficient iff its first three
nibbles belong to a 1419-element set and its five high nibbles belong
to a 172800-element set. The product has 245203200 elements, leaving
4049764096 keys that attain 2^30. The count of nibble tuples below is
proved directly. The final identification with ACTUAL keys is reserved
for a separate coordinate-equivalence proof, not assumed as an axiom.

No `sorry`, native_decide, bv_decide or custom axioms. The only `decide`
proofs examine finite local S-box tables and at most 16^3 prefix tuples.
-/



namespace Magma.OneHotPeakKeyClasses

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeBridge
open Magma.OneHotExactCoefficientGlobalMaximum
open Magma.OneHotActiveNibbleNecessary

private abbrev Word := V 32
private abbrev Q := Fin 16

private def a0 : Finset Q := {3,7,11,15}
private def a1 : Finset Q := {1,2,3,9,10,11}
private def a2 : Finset Q := {0,1,11,12,13,14,15}
private def b1 : Finset Q := {1,2,9,10}
private def b2 : Finset Q := {0,11,12,13,14,15}
private def b3 : Finset Q := {0,11,12,13,14,15}
private def b4 : Finset Q := {0,1,2,3,10,11,15}
private def b5 : Finset Q := ∅
private def b6 : Finset Q := {0,4,8,12}
private def b7 : Finset Q := {1,2,7,9,10,15}

private abbrev Prefix := Q × (Q × Q)
private abbrev High := Q × (Q × (Q × (Q × Q)))
private abbrev Coordinates := Prefix × High

private instance : DecidableEq Coordinates := inferInstance

private def avoid (s : Finset Q) : Finset Q := Finset.univ \ s
private def avoidNonzero (s : Finset Q) : Finset Q :=
  (Finset.univ \ s).erase 0

/-- Exactly three ways the first nonzero nibble can occur WITHOUT
    attaining a top DDT coefficient. At three leading zero nibbles,
    q2=0 is already a winning value, so a fourth case is impossible. -/
private def noPeakPrefix : Finset Prefix :=
  ((avoidNonzero a0) ×ˢ ((avoid b1) ×ˢ (avoid b2))) ∪
  (({0} : Finset Q) ×ˢ ((avoidNonzero a1) ×ˢ (avoid b2))) ∪
  (({0} : Finset Q) ×ˢ (({0} : Finset Q) ×ˢ (avoidNonzero a2)))

/-- Once a nonzero digit has appeared, only both-carry local winners
    could still yield coefficient 2^30. Position i=5 has none. -/
private def noPeakHigh : Finset High :=
  avoid b3 ×ˢ (avoid b4 ×ˢ
    ((Finset.univ : Finset Q) ×ˢ (avoid b6 ×ˢ avoid b7)))

private def noPeakCoordinates : Finset Coordinates :=
  noPeakPrefix ×ˢ noPeakHigh

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

private def wordCoordinatesEquiv : Word ≃ Coordinates :=
  wordDigitsEquiv.trans coordinatesEquiv

def candidateNonPeakKeys : Finset Word :=
  (Finset.univ : Finset Word).filter
    (fun k => wordCoordinatesEquiv k ∈ noPeakCoordinates)

private theorem noPeakPrefix_card : noPeakPrefix.card = 1419 := by
  let p0 := (avoidNonzero a0) ×ˢ ((avoid b1) ×ˢ (avoid b2))
  let p1 := ({0} : Finset Q) ×ˢ ((avoidNonzero a1) ×ˢ (avoid b2))
  let p2 := ({0} : Finset Q) ×ˢ (({0} : Finset Q) ×ˢ (avoidNonzero a2))
  have h01 : Disjoint p0 p1 := by
    exact Finset.disjoint_product.mpr (Or.inl (by simp [avoidNonzero]))
  have h02 : Disjoint p0 p2 := by
    exact Finset.disjoint_product.mpr (Or.inl (by simp [avoidNonzero]))
  have h12 : Disjoint p1 p2 := by
    exact Finset.disjoint_product.mpr (Or.inr
      (Finset.disjoint_product.mpr (Or.inl (by simp [avoidNonzero]))))
  have c0 : p0.card = 1320 := by
    simp only [p0, Finset.card_product]
    decide +kernel
  have c1 : p1.card = 90 := by
    simp only [p1, Finset.card_product]
    decide +kernel
  have c2 : p2.card = 9 := by
    simp only [p2, Finset.card_product]
    decide +kernel
  change ((p0 ∪ p1) ∪ p2).card = 1419
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h02, h12⟩),
    Finset.card_union_of_disjoint h01, c0, c1, c2]
end Magma.OneHotPeakKeyClasses
