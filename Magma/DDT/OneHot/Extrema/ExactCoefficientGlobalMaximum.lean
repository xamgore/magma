module

public import Magma.DDT.OneHot.Mechanics.DiagonalQuantitativeBridge
import all Init.Data.Range.Basic
import Magma.DDT.OneHot.Support.ActiveNibbleNecessary

@[expose] public section

/-!
Magma: SHARP global bound for one-hot -> one-hot one-round XOR-DDT.

The quantitative factorization from DiagonalQuantitativeBridge is used
as a THEOREM, not as an unverified implementation assumption.

For every 32-bit key and any pair of one-hot differences:
  DDT_g[k](2^j,2^ell) <= 2^30.
The bound is attained with k=3, j=1, ell=11.

For a diagonal cell (i,r,s), equality holds exactly when:
  L_i(q,0,r,s)=4 and (K_i=0 or L_i(q,1,r,s)=4),
where q=wordDigits k i and K_i=k mod 16^i.

 The eight finite local checks enumerate only small
four-bit S-box transition tables.

-/

namespace Magma.OneHotExactCoefficientGlobalMaximum

open Magma
open Magma.CarryAutomaton
open Magma.OneHotDiagonalExactWeights
open Magma.OneHotDiagonalQuantitativeBridge
open Magma.OneHotActiveNibbleNecessary

private abbrev Word :=
  V 32

/-! ## I. The LOCAL sharp ceiling is 4 for every carry and S-box. -/

private theorem local_le_four_0 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (0 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_1 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (1 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_2 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (2 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_3 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (3 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_4 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (4 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_5 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (5 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_6 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (6 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

private theorem local_le_four_7 :
    ∀ (q : Fin 16) (c : Fin 2) (r s : Fin 4), localMultiplicity (7 : Fin 8) q c r s ≤ 4 := by
  decide +kernel

/-- The only finite S-box fact needed for the global DDT maximum. -/
theorem localMultiplicity_le_four (i : Fin 8) (q : Fin 16)
    (c : Fin 2) (r s : Fin 4) :
    localMultiplicity i q c r s ≤ 4 := by
  fin_cases i
  · exact local_le_four_0 q c r s
  · exact local_le_four_1 q c r s
  · exact local_le_four_2 q c r s
  · exact local_le_four_3 q c r s
  · exact local_le_four_4 q c r s
  · exact local_le_four_5 q c r s
  · exact local_le_four_6 q c r s
  · exact local_le_four_7 q c r s

/-! ## II. The closed numerical weight is bounded by 2^30. -/

private theorem fullScale (i : Fin 8) : suffixFactor i * (lowBase i * 4) = 2 ^ 30 := by
  have hi : (7 - i.val) + i.val = 7 := by omega
  change 16 ^ (7 - i.val) * (16 ^ i.val * 4) = 2 ^ 30
  rw [← mul_assoc, ← pow_add, hi]
  norm_num

private theorem prefix_lt (k : Word) (i : Fin 8) : keyPrefix k i < lowBase i := by
  unfold keyPrefix
  exact Nat.mod_lt _ (by simp [lowBase])

/-- Every diagonal one-hot-to-one-hot coefficient is at most 2^30. -/
theorem diagonalWeight_le_two_pow_30
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    diagonalWeight k i r s ≤ 2 ^ 30 := by
  let B := lowBase i
  let K := keyPrefix k i
  let S := suffixFactor i
  let A := localMultiplicity i (wordDigits k i) 0 r s
  let C := localMultiplicity i (wordDigits k i) 1 r s
  have hK : K < B := prefix_lt k i
  have hA : A ≤ 4 := localMultiplicity_le_four i _ _ r s
  have hC : C ≤ 4 := localMultiplicity_le_four i _ _ r s
  have hsum : (B-K) * A + K * C ≤ B * 4 := by
    have h₀ := Nat.mul_le_mul_left (B-K) hA
    have h₁ := Nat.mul_le_mul_left K hC
    have hcombine : (B-K) * 4 + K * 4 = B * 4 := by
      rw [← add_mul]
      congr 1
      omega
    omega
  have hfull : S * (B*4) = 2 ^ 30 := fullScale i
  calc
    diagonalWeight k i r s =
        S * ((B-K)*A + K*C) := rfl
    _ ≤ S * (B*4) := Nat.mul_le_mul_left S hsum
    _ = 2 ^ 30 := hfull

/-! ## III. A necessary and sufficient KEY-DEPENDENT equality criterion. -/

/-- A diagonal cell reaches the global maximum iff its zero-carry
    local count is 4, and the one-carry count is also 4 whenever
    the incoming carry 1 occurs for a positive number of prefixes. -/
theorem diagonalWeight_eq_two_pow_30_iff
    (k : Word) (i : Fin 8) (r s : Fin 4) :
    diagonalWeight k i r s = 2 ^ 30 ↔
      localMultiplicity i (wordDigits k i) 0 r s = 4 ∧
      (keyPrefix k i = 0 ∨
        localMultiplicity i (wordDigits k i) 1 r s = 4) := by
  let B := lowBase i
  let K := keyPrefix k i
  let S := suffixFactor i
  let A := localMultiplicity i (wordDigits k i) 0 r s
  let C := localMultiplicity i (wordDigits k i) 1 r s
  have hK : K < B := prefix_lt k i
  have hB : 0 < B := by simp [B, lowBase]
  have hBK : 0 < B-K := by omega
  have hS : 0 < S := by simp [S, suffixFactor]
  have hA : A ≤ 4 := localMultiplicity_le_four i _ _ r s
  have hC : C ≤ 4 := localMultiplicity_le_four i _ _ r s
  have hfull : S * (B*4) = 2 ^ 30 := fullScale i
  change diagonalWeight k i r s = 2 ^ 30 ↔ A = 4 ∧ (K = 0 ∨ C = 4)
  constructor
  · intro hh
    have hw : S * ((B-K)*A + K*C) = S * (B*4) := by
      calc
        S * ((B-K)*A + K*C) = diagonalWeight k i r s := rfl
        _ = 2 ^ 30 := hh
        _ = S * (B*4) := hfull.symm
    have hsum : (B-K)*A + K*C = B*4 :=
      Nat.eq_of_mul_eq_mul_left hS hw
    have hA4 : A = 4 := by
      by_contra hne
      have hlt : A < 4 := by omega
      have hs₀ : (B-K)*A < (B-K)*4 :=
        Nat.mul_lt_mul_of_pos_left hlt hBK
      have hs₁ : K*C ≤ K*4 := Nat.mul_le_mul_left _ hC
      have htotal : (B-K)*4 + K*4 = B*4 := by
        rw [← add_mul]
        congr 1
        omega
      omega
    refine ⟨hA4, ?_⟩
    by_cases hK0 : K = 0
    · exact Or.inl hK0
    · right
      have hKpos : 0 < K := by omega
      by_contra hc4
      have hlt : C < 4 := by omega
      have hs₀ : K*C < K*4 :=
        Nat.mul_lt_mul_of_pos_left hlt hKpos
      have hs₁ : (B-K)*A ≤ (B-K)*4 :=
        Nat.mul_le_mul_left _ hA
      have htotal : (B-K)*4 + K*4 = B*4 := by
        rw [← add_mul]
        congr 1
        omega
      omega
  · rintro ⟨hA4, hrest⟩
    have hsum : (B-K)*A + K*C = B*4 := by
      rcases hrest with hK0 | hC4
      · rw [hA4, hK0]
        simp
      · rw [hA4, hC4, ← add_mul]
        congr 1
        omega
    calc
      diagonalWeight k i r s =
          S * ((B-K)*A + K*C) := rfl
      _ = S * (B*4) := by rw [hsum]
      _ = 2 ^ 30 := hfull

/-! ## IV. A SHARP witness and the full 32x32 bound. -/

/-- A local exact value; this closed check is meaningful because it
    witnesses sharpness of the global theorem. -/
private theorem sharp_local_four :
    localMultiplicity (0 : Fin 8) (3 : Fin 16) 0
      (1 : Fin 4) (0 : Fin 4) = 4 := by decide +kernel

/-- k=3, input difference 2, output difference 2^11: sharp. -/
theorem sharp_DDT_witness :
    xorDDT_g (3#32) (2#32) (0x00000800#32) = 2 ^ 30 := by
  have h := diagonal_DDT_exact
    (3#32) (0 : Fin 8) (1 : Fin 4) (0 : Fin 4)
  change xorDDT_g (3#32) (2#32) (0x00000800#32) = _ at h
  rw [h]
  have hq : wordDigits (3#32) (0 : Fin 8) = (3 : Fin 16) := by decide +kernel
  simp [diagonalWeight, keyPrefix, lowBase, suffixFactor,
    hq, sharp_local_four]

private theorem unrotate_oneHot (ell : Fin 32) :
    rot11 (BitVec.ofNat 32 (2 ^ ((ell.val + 21) % 32))) = BitVec.ofNat 32 (2 ^ ell.val) := by
  fin_cases ell <;> decide

/-- EVERY one-hot-to-one-hot DDT coefficient is bounded by 2^30,
    including all off-diagonal bit positions. -/
theorem all_oneHot_DDT_le_two_pow_30
    (k : Word) (j ell : Fin 32) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
      (BitVec.ofNat 32 (2 ^ ell.val)) ≤ 2 ^ 30 := by
  by_cases hdiag : ((ell.val + 21) % 32) / 4 = j.val / 4
  · let i : Fin 8 := ⟨j.val / 4, by omega⟩
    let r : Fin 4 := ⟨j.val % 4, by omega⟩
    let s : Fin 4 := ⟨((ell.val + 21) % 32) % 4, by omega⟩
    have hj : 4 * i.val + r.val = j.val := by
      dsimp [i, r]
      omega
    have hs : 4 * i.val + s.val = (ell.val + 21) % 32 := by
      dsimp [i, s]
      omega
    have hrot :
        rot11 (BitVec.ofNat 32 (2 ^ (4*i.val+s.val))) =
          BitVec.ofNat 32 (2 ^ ell.val) := by
      rw [hs]
      exact unrotate_oneHot ell
    have hweight := diagonal_DDT_exact k i r s
    change xorDDT_g k (BitVec.ofNat 32 (2 ^ (4 * i.val + r.val)))
      (rot11 (BitVec.ofNat 32 (2 ^ (4 * i.val + s.val)))) =
        diagonalWeight k i r s at hweight
    rw [hj, hrot] at hweight
    rw [hweight]
    exact diagonalWeight_le_two_pow_30 k i r s
  · have hz := oneHot_matrix_off_diagonal_zero k j ell hdiag
    rw [hz]
    norm_num

/-- A complete, SHARP answer to the global one-hot coefficient
    maximization problem: all keys and all 1024 bit-position pairs. -/
theorem global_oneHot_maximum_exact :
    (∀ (k : Word) (j ell : Fin 32),
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ ell.val)) ≤ 2 ^ 30) ∧
    (∃ (k : Word) (j ell : Fin 32),
      xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val))
        (BitVec.ofNat 32 (2 ^ ell.val)) = 2 ^ 30) := by
  constructor
  · exact all_oneHot_DDT_le_two_pow_30
  · refine ⟨3#32, (⟨1, by omega⟩ : Fin 32),
      (⟨11, by omega⟩ : Fin 32), ?_⟩
    simpa using sharp_DDT_witness

end Magma.OneHotExactCoefficientGlobalMaximum
