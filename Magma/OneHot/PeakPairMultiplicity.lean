module

public import Magma.OneHot.PeakKeyClassesSemanticClosure
import all Init.Data.Range.Basic

@[expose] public section

/-!
The number and POSITIONS of globally maximizing one-hot -> one-hot
DDT coefficients at a FIXED 32-bit Magma round key.

There are 1024 possible (j,ell) pairs. A DDT coefficient equals 2^30
only in a diagonal nibble block, so the entire list of maximizing pairs
is an injective image of at most 128 (i,r,s) triples. This module proves
an EXACT set identity and a cardinality identity, not a Boolean heuristic.

The next intended step is to prove a global MAXIMUM of EIGHT such pairs
per key (computed separately by a 2-state nibble dynamic program).

No existing private declarations need to be promoted to public.
No sorry, native_decide, or new axioms.
-/

namespace Magma.OneHotPeakPairMultiplicity

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeBridge
open Magma.OneHotExactCoefficientGlobalMaximum
open Magma.OneHotActiveNibbleNecessary

private abbrev Word :=
  V 32

private abbrev Local :=
  Fin 8 × (Fin 4 × Fin 4)

private abbrev Global :=
  Fin 32 × Fin 32

/-- Actual (input bit, output bit) positions attaining the proven sharp
    one-round coefficient 2^30 at this particular round key. -/
def actualPeakPairs (k : Word) : Finset Global :=
  Finset.univ.filter (fun p =>
    xorDDT_g k (BitVec.ofNat 32 (2 ^ p.1.val))
      (BitVec.ofNat 32 (2 ^ p.2.val)) = 2 ^ 30)

/-- Corresponding set of local maximizing positions (nibble, in-bit,
    out-bit before the 11-bit rotation). No 32-bit DDT enumeration. -/
def localPeakPairs (k : Word) : Finset Local :=
  Finset.univ.filter (fun p =>
    diagonalWeight k p.1 p.2.1 p.2.2 = 2 ^ 30)

/-- Convert local coordinates to the two original global bit indices. -/
def encode (p : Local) : Global :=
  (⟨4 * p.1.val + p.2.1.val, by omega⟩,
   ⟨(4 * p.1.val + p.2.2.val + 11) % 32, by omega⟩)

private theorem rotated_output_at (i : Fin 8) (s : Fin 4) :
    rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val))) =
      BitVec.ofNat 32 (2 ^ ((4 * i.val + s.val + 11) % 32)) := by
  fin_cases i <;> fin_cases s <;> decide

/-- Every local entry computes the true DDT at exactly the encoded
    global bit positions. -/
theorem encoded_entry_exact (k : Word) (p : Local) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (encode p).1.val))
      (BitVec.ofNat 32 (2 ^ (encode p).2.val)) =
        diagonalWeight k p.1 p.2.1 p.2.2 := by
  rcases p with ⟨i, ⟨r,s⟩⟩
  change xorDDT_g k (BitVec.ofNat 32 (2 ^ (4*i.val+r.val)))
    (BitVec.ofNat 32 (2 ^ ((4*i.val+s.val+11) % 32))) =
      diagonalWeight k i r s
  have h := diagonal_DDT_exact k i r s
  change xorDDT_g k (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
    (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) =
      diagonalWeight k i r s at h
  rw [rotated_output_at i s] at h
  exact h

/-- Distinct local triples always give distinct input/output bit pairs. -/
theorem encode_injective : Function.Injective encode := by
  intro ⟨i,⟨r,s⟩⟩ ⟨i',⟨r',s'⟩⟩ h
  have hj : 4*i.val+r.val = 4*i'.val+r'.val :=
    congrArg (fun z : Global => z.1.val) h
  have he : (4*i.val+s.val+11)%32 =
      (4*i'.val+s'.val+11)%32 :=
    congrArg (fun z : Global => z.2.val) h
  have hi : i = i' := Fin.ext (by omega)
  have hr : r = r' := Fin.ext (by omega)
  have hs : s = s' := Fin.ext (by omega)
  cases hi
  cases hr
  cases hs
  rfl

/-- Every pair of global indices in the same nibble block (after
    undoing rotation) has a UNIQUE local encoding. -/
private theorem decode_diagonal (j ell : Fin 32)
    (hdiag : ((ell.val+21)%32)/4 = j.val/4) :
    ∃ p : Local, encode p = (j,ell) := by
  let i : Fin 8 := ⟨j.val/4, by omega⟩
  let r : Fin 4 := ⟨j.val%4, by omega⟩
  let s : Fin 4 := ⟨((ell.val+21)%32)%4, by omega⟩
  have hj : 4*i.val+r.val=j.val := by dsimp [i,r]; omega
  have he : 4*i.val+s.val=(ell.val+21)%32 := by
    dsimp [i,s]
    omega
  have hrot : (4*i.val+s.val+11)%32=ell.val := by
    rw [he]
    have hell := ell.isLt
    omega
  refine ⟨(i,(r,s)), ?_⟩
  apply Prod.ext
  · apply Fin.ext
    exact hj
  · apply Fin.ext
    exact hrot

/-- The entire set of actual top-DDT bit pairs is the injective
    image of a finite set of at most 128 local triples. -/
theorem actualPeakPairs_eq_image (k : Word) :
    actualPeakPairs k = (localPeakPairs k).image encode := by
  classical
  ext p
  rcases p with ⟨j,ell⟩
  constructor
  · intro hp
    have htop : xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ ell.val)) = 2 ^ 30 :=
      (Finset.mem_filter.mp hp).2
    have hdiag : ((ell.val+21)%32)/4 = j.val/4 := by
      by_contra hn
      have hz := oneHot_matrix_off_diagonal_zero k j ell hn
      rw [hz] at htop
      norm_num at htop
    obtain ⟨q,hq⟩ := decode_diagonal j ell hdiag
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, hq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he := encoded_entry_exact k q
    rw [hq] at he
    exact he.symm.trans htop
  · intro hp
    obtain ⟨q,hq,hencode⟩ := Finset.mem_image.mp hp
    have hlocal : diagonalWeight k q.1 q.2.1 q.2.2 = 2 ^ 30 :=
      (Finset.mem_filter.mp hq).2
    have he := encoded_entry_exact k q
    rw [hencode] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.trans hlocal⟩

/-- Main exact multiplicity theorem, for EVERY one-round key. -/
theorem actualPeakPairs_card_eq_local (k : Word) :
    (actualPeakPairs k).card = (localPeakPairs k).card := by
  rw [actualPeakPairs_eq_image]
  exact Finset.card_image_of_injective _ encode_injective

/-- The per-cell test can use only TWO tiny local multiplicities,
    without the large DDT or its numeric `diagonalWeight`. -/
theorem localPeakPairs_mem_iff (k : Word) (i : Fin 8)
    (r s : Fin 4) :
    (i,(r,s)) ∈ localPeakPairs k ↔
      localMultiplicity i (wordDigits k i) 0 r s = 4 ∧
        (keyPrefix k i = 0 ∨
          localMultiplicity i (wordDigits k i) 1 r s = 4) := by
  simp only [localPeakPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact diagonalWeight_eq_two_pow_30_iff k i r s

/-- Equivalence to the previously kernel-proved existential key test.
    If there is no coefficient of 2^30, the count is exactly zero. -/
theorem actualPeakPairs_nonempty_iff (k : Word) :
    (actualPeakPairs k).Nonempty ↔
      Magma.OneHotPeakKeyClasses.hasPeakCoefficient k := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p.1,p.2,(Finset.mem_filter.mp hp).2⟩
  · rintro ⟨j,ell,hj⟩
    exact ⟨(j,ell), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hj⟩⟩

/-- Zero maximizing pairs are EXACTLY the keys excluded by the
    previously proved semantic key classification. -/
theorem zero_peak_pairs_iff (k : Word) :
    (actualPeakPairs k).card = 0 ↔
      ¬ Magma.OneHotPeakKeyClasses.hasPeakCoefficient k := by
  rw [Finset.card_eq_zero]
  constructor
  · intro he hn
    obtain ⟨p, hp⟩ := (actualPeakPairs_nonempty_iff k).mpr hn
    rw [he] at hp
    simp at hp
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h ((actualPeakPairs_nonempty_iff k).mp ⟨p, hp⟩)

/-- Consistency check with the established classification of all
    nonmaximizing actual 32-bit keys (without enumerating those keys). -/
theorem zero_peak_pairs_key_count :
    ((Finset.univ : Finset Word).filter
       (fun k => (actualPeakPairs k).card = 0)).card = 245203200 := by
  calc
    ((Finset.univ : Finset Word).filter
       (fun k => (actualPeakPairs k).card = 0)).card =
         Magma.OneHotPeakKeyClasses.candidateNonPeakKeys.card := by
           apply congrArg Finset.card
           ext k
           simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Magma.OneHotPeakKeyClasses.candidateNonPeakKeys]
           rw [zero_peak_pairs_iff,
             Magma.OneHotPeakKeyClasses.no_peak_iff_coordinates]
    _ = 245203200 :=
      Magma.OneHotPeakKeyClasses.candidateNonPeakKeys_card

/-- A substantive witness: this 32-bit round key has eight distinct
    maximum-strength one-hot transitions. This verifies a closed LOCAL
    expression rather than enumerating the full 32-bit DDT. -/
theorem eight_peak_pairs_witness :
    (actualPeakPairs (0x10020020#32)).card = 8 := by
  rw [actualPeakPairs_card_eq_local]
  decide +kernel

end Magma.OneHotPeakPairMultiplicity
