module

public import Magma.OneHot.DiagonalCarryMasks
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Sharp one-hot candidate support over all round keys

Each of the 76 locally permitted bit-position pairs has an explicit key
and input witness, checked against the original RFC round function `g`.
Both witness words have at most one nonzero nibble.

Thus `candidateCell` is equivalent to positivity for some round key:
exactly 76 cells are realizable over the union of keys, and exactly 948
are zero for every key. Finite checks verify the supplied witnesses;
no full-word search is performed.
-/

namespace Magma.OneHotCandidateSharp

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalCarryMasks

private abbrev Word :=
  V 32

/-- Source bit 4*i+r, before modular addition. -/
private def srcBit (i : Fin 8) (r : Fin 4) : Fin 32 :=
  ⟨4 * i.val + r.val, by omega⟩

/-- Target bit 4*i+s, AFTER the 11-bit rotation of g. -/
private def dstBit (i : Fin 8) (s : Fin 4) : Fin 32 :=
  ⟨(4 * i.val + s.val + 11) % 32, by omega⟩

/-- A fixed local key-digit/input-digit witness for every permitted
    local output bit. Non-candidate triples default to (0,0) and are
    never used in proofs of positivity. -/
def witnessDigits (i : Fin 8) (r s : Fin 4) : Fin 16 × Fin 16 :=
  match i.val, r.val, s.val with
  | 0, 0, 1 => (0, 6)
  | 0, 0, 2 => (0, 2)
  | 0, 0, 3 => (0, 0)
  | 0, 1, 0 => (0, 4)
  | 0, 1, 1 => (0, 13)
  | 0, 1, 2 => (2, 9)
  | 0, 2, 0 => (0, 1)
  | 0, 2, 1 => (0, 10)
  | 0, 2, 2 => (1, 3)
  | 0, 3, 1 => (0, 0)
  | 0, 3, 2 => (0, 6)
  | 0, 3, 3 => (0, 7)
  | 1, 0, 0 => (0, 2)
  | 1, 1, 1 => (0, 13)
  | 1, 1, 2 => (0, 0)
  | 1, 2, 0 => (3, 3)
  | 1, 2, 1 => (0, 1)
  | 1, 2, 2 => (0, 10)
  | 1, 2, 3 => (0, 11)
  | 1, 3, 1 => (0, 4)
  | 1, 3, 2 => (0, 3)
  | 2, 0, 3 => (0, 0)
  | 2, 1, 1 => (0, 5)
  | 2, 1, 2 => (1, 5)
  | 2, 1, 3 => (0, 4)
  | 2, 2, 0 => (0, 10)
  | 2, 2, 1 => (0, 8)
  | 2, 2, 2 => (0, 11)
  | 2, 2, 3 => (0, 9)
  | 2, 3, 1 => (0, 1)
  | 3, 0, 0 => (1, 6)
  | 3, 0, 1 => (0, 14)
  | 3, 0, 2 => (0, 0)
  | 3, 1, 1 => (0, 4)
  | 3, 1, 3 => (1, 5)
  | 3, 2, 0 => (0, 0)
  | 3, 2, 2 => (0, 8)
  | 3, 3, 2 => (0, 3)
  | 3, 3, 3 => (0, 1)
  | 4, 0, 1 => (1, 2)
  | 4, 0, 3 => (0, 0)
  | 4, 1, 1 => (0, 0)
  | 4, 1, 2 => (2, 5)
  | 4, 1, 3 => (0, 13)
  | 4, 2, 0 => (0, 10)
  | 4, 2, 1 => (0, 11)
  | 4, 2, 3 => (1, 3)
  | 4, 3, 0 => (0, 7)
  | 4, 3, 2 => (0, 3)
  | 5, 0, 0 => (1, 6)
  | 5, 0, 1 => (1, 0)
  | 5, 0, 3 => (0, 0)
  | 5, 1, 1 => (2, 9)
  | 5, 1, 2 => (2, 1)
  | 5, 1, 3 => (0, 5)
  | 5, 2, 0 => (0, 11)
  | 5, 2, 1 => (1, 3)
  | 5, 2, 2 => (0, 9)
  | 5, 3, 0 => (0, 5)
  | 5, 3, 1 => (0, 6)
  | 6, 0, 2 => (0, 14)
  | 6, 0, 3 => (1, 4)
  | 6, 1, 2 => (0, 8)
  | 6, 1, 3 => (2, 5)
  | 6, 2, 1 => (0, 8)
  | 6, 2, 3 => (0, 10)
  | 6, 3, 1 => (0, 6)
  | 7, 1, 1 => (0, 12)
  | 7, 1, 3 => (0, 4)
  | 7, 2, 0 => (0, 0)
  | 7, 2, 1 => (0, 1)
  | 7, 2, 2 => (0, 11)
  | 7, 2, 3 => (1, 11)
  | 7, 3, 0 => (0, 7)
  | 7, 3, 2 => (0, 2)
  | 7, 3, 3 => (0, 1)
  | _, _, _ => (0, 0)

/-- Explicit 32-bit key containing just the chosen active nibble. -/
def witnessKey (i : Fin 8) (r s : Fin 4) : Word :=
  BitVec.ofNat 32 ((witnessDigits i r s).1.val * 16 ^ i.val)

/-- Explicit input word containing just the chosen active nibble. -/
def witnessInput (i : Fin 8) (r s : Fin 4) : Word :=
  BitVec.ofNat 32 ((witnessDigits i r s).2.val * 16 ^ i.val)

/-- Verify the exact output difference of each of the 76 explicit
    witnesses against the ORIGINAL RFC function `g`, not a local model.
    Each goal is a closed 32-bit computation. The remaining 52 cases
    are excluded by their previously certified masks. -/
theorem witness_correct (i : Fin 8) (r s : Fin 4)
    (h : maskAllows i r s) :
    xor (g (witnessKey i r s)
      (xor (witnessInput i r s)
        (BitVec.ofNat 32 (2 ^ (srcBit i r).val))))
      (g (witnessKey i r s) (witnessInput i r s)) =
        BitVec.ofNat 32 (2 ^ (dstBit i s).val) := by
  revert i r s
  decide +kernel

/-- The local mask condition is SUFFICIENT for positive DDT at
    some round key. The witness is a concrete 32-bit input word. -/
theorem permitted_local_has_real_key (i : Fin 8) (r s : Fin 4)
    (h : maskAllows i r s) :
    0 < xorDDT_g (witnessKey i r s)
      (BitVec.ofNat 32 (2 ^ (srcBit i r).val))
      (BitVec.ofNat 32 (2 ^ (dstBit i s).val)) := by
  unfold xorDDT_g
  apply Finset.card_pos.mpr
  refine ⟨witnessInput i r s, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, witness_correct i r s h⟩

/-- Unrotating and separating the 32 bit indices gives a UNIQUE local
    nibble triple i,r,s, as soon as `candidateCell` holds. -/
private theorem candidateCell_as_triple (j ell : Fin 32)
    (h : candidateCell j ell) :
    ∃ (i : Fin 8) (r s : Fin 4),
      j = srcBit i r ∧ ell = dstBit i s ∧ maskAllows i r s := by
  unfold candidateCell at h
  dsimp at h
  let i : Fin 8 := ⟨j.val / 4, by omega⟩
  let r : Fin 4 := ⟨j.val % 4, by omega⟩
  let s : Fin 4 := ⟨((ell.val + 21) % 32) % 4, by omega⟩
  refine ⟨i, r, s, ?_, ?_, ?_⟩
  · apply Fin.ext
    dsimp [srcBit, i, r]
    omega
  · apply Fin.ext
    dsimp [dstBit, i, s]
    omega
  · exact h.2

/-- SHARP SUPPORT CLASSIFICATION OVER ALL KEYS.

    A 32×32 one-hot DDT cell is positive for SOME Magma round key
    if and only if the 4-bit candidate mask permits the cell.
    In particular, there are precisely 76 realizable cells, 948
    universally impossible cells. -/
theorem candidateCell_iff_exists_positive_key (j ell : Fin 32) :
    candidateCell j ell ↔
      ∃ k : Word,
        0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
          (BitVec.ofNat 32 (2 ^ ell.val)) := by
  constructor
  · intro h
    obtain ⟨i, r, s, hj, hell, hm⟩ := candidateCell_as_triple j ell h
    refine ⟨witnessKey i r s, ?_⟩
    rw [hj, hell]
    exact permitted_local_has_real_key i r s hm
  · rintro ⟨k, hp⟩
    by_contra h
    have hz := oneHot_DDT_zero_of_not_candidate k j ell h
    omega

/-- This is the number of all pairs (j,ell) for which a positive
    transition exists for AT LEAST ONE round key. -/
theorem realizable_oneHot_cells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => ∃ k : Word,
        0 < xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)))).card = 76 := by
  classical
  have heq :
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => ∃ k : Word,
          0 < xorDDT_g k
            (BitVec.ofNat 32 (2 ^ p.1.val))
            (BitVec.ofNat 32 (2 ^ p.2.val)))) =
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => candidateCell p.1 p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (candidateCell_iff_exists_positive_key p.1 p.2).symm
  rw [heq]
  exact candidateCells_card

/-- Complementary exact count: exactly 948 one-hot bit pairs have
    zero DDT for EVERY possible 32-bit round key. -/
theorem universally_impossible_oneHot_cells_card :
    ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
      (fun p : Fin 32 × Fin 32 => ∀ k : Word,
        xorDDT_g k
          (BitVec.ofNat 32 (2 ^ p.1.val))
          (BitVec.ofNat 32 (2 ^ p.2.val)) = 0)).card = 948 := by
  classical
  have heq :
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => ∀ k : Word,
          xorDDT_g k
            (BitVec.ofNat 32 (2 ^ p.1.val))
            (BitVec.ofNat 32 (2 ^ p.2.val)) = 0)) =
      ((Finset.univ : Finset (Fin 32 × Fin 32)).filter
        (fun p : Fin 32 × Fin 32 => ¬candidateCell p.1 p.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz hc
      obtain ⟨k, hp⟩ := (candidateCell_iff_exists_positive_key p.1 p.2).mp hc
      have hzero := hz k
      omega
    · intro hn k
      exact oneHot_DDT_zero_of_not_candidate k p.1 p.2 hn
  rw [heq]
  exact excludedCells_card

end Magma.OneHotCandidateSharp
