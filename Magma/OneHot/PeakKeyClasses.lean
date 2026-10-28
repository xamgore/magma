module

public import Magma.OneHot.ExactCoefficientGlobalMaximum
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

 The only `decide`
proofs examine finite local S-box tables and at most 16^3 prefix tuples.
-/

namespace Magma.OneHotPeakKeyClasses

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeBridge
open Magma.OneHotExactCoefficientGlobalMaximum
open Magma.OneHotActiveNibbleNecessary

abbrev Word :=
  V 32

abbrev Q :=
  Fin 16

/-- A nibble value for which *some* bit pair reaches local count four
    with incoming carry zero. -/
def zeroPeakClass (i : Fin 8) : Finset Q :=
  Finset.univ.filter (fun q =>
    ∃ (r s : Fin 4), localMultiplicity i q 0 r s = 4)

/-- A nibble value with a bit pair that reaches four for BOTH incoming
    carries. A nonzero lower key prefix requires this stronger condition. -/
def bothPeakClass (i : Fin 8) : Finset Q :=
  Finset.univ.filter (fun q =>
    ∃ (r s : Fin 4),
      localMultiplicity i q 0 r s = 4 ∧
      localMultiplicity i q 1 r s = 4)

/-- Exact positions in the one-round DDT attaining 2^30. -/
def hasPeakCoefficient (k : Word) : Prop :=
  ∃ j ell : Fin 32,
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) = 2 ^ 30

/-- Uniform local criterion for the top coefficient in a diagonal block. -/
theorem diagonal_peak_iff_class (k : Word) (i : Fin 8) :
    (∃ (r s : Fin 4), diagonalWeight k i r s = 2 ^ 30) ↔
      (if keyPrefix k i = 0 then
        wordDigits k i ∈ zeroPeakClass i
       else wordDigits k i ∈ bothPeakClass i) := by
  by_cases hK : keyPrefix k i = 0
  · simp only [hK, ite_true]
    simp only [zeroPeakClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, s, h⟩
      exact ⟨r, s, ((diagonalWeight_eq_two_pow_30_iff k i r s).mp h).1⟩
    · rintro ⟨r, s, h⟩
      exact ⟨r, s, (diagonalWeight_eq_two_pow_30_iff k i r s).mpr
        ⟨h, Or.inl hK⟩⟩
  · simp only [ite_eq_right hK]
    simp only [bothPeakClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, s, h⟩
      have hh := (diagonalWeight_eq_two_pow_30_iff k i r s).mp h
      exact ⟨r, s, hh.1, hh.2.resolve_left hK⟩
    · rintro ⟨r, s, h0, h1⟩
      exact ⟨r, s, (diagonalWeight_eq_two_pow_30_iff k i r s).mpr
        ⟨h0, Or.inr h1⟩⟩

/-- For any key, determining the EXISTENCE of a maximum coefficient
    requires only eight local 16-element tables and the key prefixes. -/
def hasPeakLocal (k : Word) : Prop :=
  ∃ i : Fin 8,
    if keyPrefix k i = 0 then
      wordDigits k i ∈ zeroPeakClass i
    else wordDigits k i ∈ bothPeakClass i

private theorem oneHot_unpack (j ell : Fin 32) (h : (ell.val + 21) % 32 / 4 = j.val / 4) :
    ∃ (i : Fin 8) (r s : Fin 4),
      4 * i.val + r.val = j.val ∧
        rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) = BitVec.ofNat 32 (2 ^ ell.val) := by
  let i : Fin 8 := ⟨j.val / 4, by omega⟩
  let r : Fin 4 := ⟨j.val % 4, by omega⟩
  let s : Fin 4 := ⟨((ell.val + 21) % 32) % 4, by omega⟩
  have hj : 4 * i.val + r.val = j.val := by
    dsimp [i, r]; omega
  have hs : 4 * i.val + s.val = (ell.val + 21) % 32 := by
    dsimp [i, s]; omega
  have hr : rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) = BitVec.ofNat 32 (2 ^ ell.val) := by
    rw [hs]
    fin_cases ell <;> decide
  exact ⟨i, r, s, hj, hr⟩

private theorem oneHot_pack (i : Fin 8) (r s : Fin 4) :
    ∃ (j ell : Fin 32),
      BitVec.ofNat 32 (2 ^ j.val) = BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)) ∧
        BitVec.ofNat 32 (2 ^ ell.val) = rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) := by
  let j : Fin 32 := ⟨4 * i.val + r.val, by omega⟩
  let ell : Fin 32 := ⟨(4 * i.val + s.val + 11) % 32, by omega⟩
  refine ⟨j, ell, rfl, ?_⟩
  fin_cases i <;> fin_cases s <;> decide

/-- The real one-hot matrix has a globally sharp entry iff one of the
    eight actual key digits meets its exact local maximum condition. -/
theorem hasPeakCoefficient_iff_local (k : Word) :
    hasPeakCoefficient k ↔ hasPeakLocal k := by
  constructor
  · rintro ⟨j,ell,hsharp⟩
    by_cases hd : (ell.val + 21) % 32 / 4 = j.val / 4
    · obtain ⟨i,r,s,hj,he⟩ := oneHot_unpack j ell hd
      have hh := diagonal_DDT_exact k i r s
      change xorDDT_g k (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
        (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) =
          diagonalWeight k i r s at hh
      rw [hj, he] at hh
      have hweight : diagonalWeight k i r s = 2 ^ 30 := by
        rw [←hh]
        exact hsharp
      exact ⟨i, (diagonal_peak_iff_class k i).mp ⟨r,s,hweight⟩⟩
    · have hzero := oneHot_matrix_off_diagonal_zero k j ell hd
      rw [hzero] at hsharp
      omega
  · rintro ⟨i,hi⟩
    obtain ⟨r,s,hw⟩ := (diagonal_peak_iff_class k i).mpr hi
    obtain ⟨j,ell,hj,he⟩ := oneHot_pack i r s
    refine ⟨j,ell,?_⟩
    rw [hj,he]
    exact (diagonal_DDT_exact k i r s).trans hw

/-! ### Verified small local winner classes. -/

def a0 : Finset Q :=
  {3,7,11,15}

def a1 : Finset Q :=
  {1,2,3,9,10,11}

def a2 : Finset Q :=
  {0, 1, 11, 12, 13, 14, 15}

def b1 : Finset Q :=
  {1,2,9,10}

def b2 : Finset Q :=
  {0, 11, 12, 13, 14, 15}

def b3 : Finset Q :=
  {0, 11, 12, 13, 14, 15}

def b4 : Finset Q :=
  {0, 1, 2, 3, 10, 11, 15}

def b5 : Finset Q :=
  ∅

def b6 : Finset Q :=
  {0, 4, 8, 12}

def b7 : Finset Q :=
  {1,2,7,9,10,15}

theorem a0_correct : zeroPeakClass 0 = a0 := by decide +kernel

theorem a1_correct : zeroPeakClass 1 = a1 := by decide +kernel

theorem a2_correct : zeroPeakClass 2 = a2 := by decide +kernel

theorem b1_correct : bothPeakClass 1 = b1 := by decide +kernel

theorem b2_correct : bothPeakClass 2 = b2 := by decide +kernel

theorem b3_correct : bothPeakClass 3 = b3 := by decide +kernel

theorem b4_correct : bothPeakClass 4 = b4 := by decide +kernel

theorem b5_correct : bothPeakClass 5 = b5 := by decide +kernel

theorem b6_correct : bothPeakClass 6 = b6 := by decide +kernel

theorem b7_correct : bothPeakClass 7 = b7 := by decide +kernel

/-! ### Closed coordinate count for all keys WITHOUT the top DDT. -/

abbrev Prefix :=
  Q × (Q × Q)

abbrev High :=
  Q × (Q × (Q × (Q × Q)))

abbrev Coordinates :=
  Prefix × High

private instance : DecidableEq Coordinates :=
  inferInstance

def avoid (s : Finset Q) : Finset Q :=
  Finset.univ \ s

def avoidNonzero (s : Finset Q) : Finset Q :=
  (Finset.univ \ s).erase 0

/-- Exactly three ways the first nonzero nibble can occur WITHOUT
    attaining a top DDT coefficient. At three leading zero nibbles,
    q2=0 is already a winning value, so a fourth case is impossible. -/
def noPeakPrefix : Finset Prefix :=
  ((avoidNonzero a0) ×ˢ ((avoid b1) ×ˢ (avoid b2))) ∪
  (({0} : Finset Q) ×ˢ ((avoidNonzero a1) ×ˢ (avoid b2))) ∪
  (({0} : Finset Q) ×ˢ (({0} : Finset Q) ×ˢ (avoidNonzero a2)))

/-- Once a nonzero digit has appeared, only both-carry local winners
    could still yield coefficient 2^30. Position i=5 has none. -/
def noPeakHigh : Finset High :=
  avoid b3 ×ˢ (avoid b4 ×ˢ
    ((Finset.univ : Finset Q) ×ˢ (avoid b6 ×ˢ avoid b7)))

def noPeakCoordinates : Finset Coordinates :=
  noPeakPrefix ×ˢ noPeakHigh

/-- 1320 + 90 + 9 prefix combinations. All three branches are disjoint. -/
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

/-- 10 * 9 * 16 * 12 * 10 possible high five-digit suffixes. -/
private theorem noPeakHigh_card : noPeakHigh.card = 172800 := by
  have h3 : (avoid b3).card = 10 := by decide +kernel
  have h4 : (avoid b4).card = 9 := by decide +kernel
  have h6 : (avoid b6).card = 12 := by decide +kernel
  have h7 : (avoid b7).card = 10 := by decide +kernel
  simp [noPeakHigh, Finset.card_product, h3, h4, h6, h7]

/-- Exact count of nonmaximizing EIGHT-NIBBLE TUPLES, independent of
    any expensive or impossible enumeration of 2^32 keys. -/
theorem noPeakCoordinates_card : noPeakCoordinates.card = 245203200 := by
  simp [noPeakCoordinates, Finset.card_product, noPeakPrefix_card,
    noPeakHigh_card]

/-- Corresponding number of maximizing coordinate tuples, by subtraction. -/
theorem numberOfWinningTuples_arithmetic :
    2 ^ 32 - noPeakCoordinates.card = 4049764096 := by
  rw [noPeakCoordinates_card]
  norm_num

/-! ### A purely structural transfer to ACTUAL 32-bit keys. -/

def toCoordinates (d : Fin 8 → Q) : Coordinates :=
  ((d 0, d 1, d 2), (d 3, d 4, d 5, d 6, d 7))

def fromCoordinates (c : Coordinates) (i : Fin 8) : Q :=
  match i.val with
  | 0 => c.1.1
  | 1 => c.1.2.1
  | 2 => c.1.2.2
  | 3 => c.2.1
  | 4 => c.2.2.1
  | 5 => c.2.2.2.1
  | 6 => c.2.2.2.2.1
  | _ => c.2.2.2.2.2

def coordinatesEquiv : (Fin 8 → Q) ≃ Coordinates where
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

def wordCoordinatesEquiv : Word ≃ Coordinates :=
  wordDigitsEquiv.trans coordinatesEquiv

/-- An explicit subset of the REAL round keys, represented by the
    already classified 8-digit coordinate tuples. -/
def candidateNonPeakKeys : Finset Word :=
  (Finset.univ : Finset Word).filter
    (fun k => wordCoordinatesEquiv k ∈ noPeakCoordinates)

/-- Exactly 245203200 actual 32-bit words satisfy this explicit
    coordinate predicate, without evaluating any 32-bit Finset. -/
theorem candidateNonPeakKeys_card : candidateNonPeakKeys.card = 245203200 := by
  calc
    candidateNonPeakKeys.card = noPeakCoordinates.card := by
      refine Finset.card_equiv wordCoordinatesEquiv ?_
      intro k
      simp only [candidateNonPeakKeys, Finset.mem_filter, Finset.mem_univ, true_and]
    _ = 245203200 := noPeakCoordinates_card

open scoped Classical

/-- The last semantic bridge is deliberately a HYPOTHESIS, not an axiom:
    it is the single unproved obligation needed to make the arithmetic
    count a theorem about DDT maxima. This theorem does not claim the
    hypothesis is already established. -/
theorem actual_peak_key_count_of_coordinate_characterization
    (h : ∀ k : Word,
      (¬hasPeakCoefficient k) ↔
        wordCoordinatesEquiv k ∈ noPeakCoordinates) :
    ((Finset.univ : Finset Word).filter hasPeakCoefficient).card =
      4049764096 := by
  let a : Finset Word := Finset.univ.filter hasPeakCoefficient
  let b : Finset Word := Finset.univ.filter (fun k => ¬hasPeakCoefficient k)
  have hb : b.card = 245203200 := by
    calc
      b.card = candidateNonPeakKeys.card := by
        apply congrArg Finset.card
        ext k
        simp only [b, candidateNonPeakKeys, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact h k
      _ = 245203200 := candidateNonPeakKeys_card
  have hu : a ∪ b = Finset.univ := by
    ext k
    simp [a, b, or_not]
  have hd : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro k ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hsum := Finset.card_union_of_disjoint hd
  rw [hu] at hsum
  have htotal : (Finset.univ : Finset Word).card = 2 ^ 32 := by
    calc
      (Finset.univ : Finset Word).card =
          (Finset.univ : Finset Coordinates).card := by
        refine Finset.card_equiv wordCoordinatesEquiv ?_
        intro k
        simp
      _ = 2 ^ 32 := by
        simp [Coordinates, Prefix, High, Fintype.card_prod]
  change a.card = 4049764096
  omega

end Magma.OneHotPeakKeyClasses
