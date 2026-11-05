module

import all Init.Data.Range.Basic
public import Magma.Carry.Automaton

@[expose] public section

/-!
# An exact 16+16 split of the actual Magma round differential count

`Magma.CarryAutomaton` proves the complete eight-nibble
matrix product equal to `xorDDT_g`. Here we split that ordered product
after nibble 3, carrying precisely TWO addition-carry bits across the
boundary. The state type is `Fin 2 × Fin 2`, with four possibilities.

For a fixed (key, input XOR difference, unrotated output XOR difference),
  DDT = sum_(boundary state) lowerCount * upperCount.
Each factor contains four 4-bit S-box steps. Conditioning on the
boundary carries retains the dependence between the two halves.
-/

namespace Magma.DiffanGCarryHalfSplit

open Magma
open Magma.CarryAutomaton

private abbrev Word :=
  V 32

/-- Reindex a low-half digit, from 0..3 into the full index 0..7. -/
def lowIndex (i : Fin 4) : Fin 8 :=
  ⟨i.val, by omega⟩

/-- Reindex a high-half digit, from 0..3 into the full index 4..7. -/
def highIndex (i : Fin 4) : Fin 8 :=
  ⟨i.val + 4, by omega⟩

/-- The row distribution of the two carries after processing four
low-order nibbles. All four states are kept separately. -/
def lowerRow (key diff target : Fin 8 → Fin 16) : CarryState → Nat :=
  Fin.foldl 4
    (fun row i => Matrix.vecMul row
      (carryMatrix (lowIndex i)
        (key (lowIndex i)) (diff (lowIndex i)) (target (lowIndex i))))
    initialRow

/-- The ordered four-nibble transition product for the upper 16 bits.
The final carry is unrestricted, since addition is modulo 2^32. -/
def upperProduct (key diff target : Fin 8 → Fin 16) :
    Matrix CarryState CarryState Nat :=
  Fin.foldl 4
    (fun mat i => mat *
      carryMatrix (highIndex i)
        (key (highIndex i)) (diff (highIndex i)) (target (highIndex i)))
    1

/-- Number of high 16-bit input assignments accepted given the two
incoming carries. Carries after the final nibble are summed out. -/
def upperCount (key diff target : Fin 8 → Fin 16)
    (s : CarryState) : Nat :=
  ∑ t : CarryState, upperProduct key diff target s t

/-- Our two-bit interface genuinely consists of four states. -/
theorem carryState_card : Fintype.card CarryState = 4 := by decide

/-- A fixed-length ordered fold factors into its first four steps and
last four steps. This is a pure law of finite iteration. -/
private theorem foldEight_split {A : Type*}
    (step : A → Fin 8 → A) (start : A) :
    Fin.foldl 8 step start =
      Fin.foldl 4 (fun acc i => step acc (highIndex i))
        (Fin.foldl 4 (fun acc i => step acc (lowIndex i)) start) := by
  rfl

/-- Vector multiplication by a product of finite matrices coincides
with successively applying the four matrix transitions. -/
private theorem vecMul_ordered_product :
    ∀ (n : Nat) (mat : Fin n → Matrix CarryState CarryState Nat)
      (row : CarryState → Nat),
      Fin.foldl n (fun acc i => Matrix.vecMul acc (mat i)) row =
        Matrix.vecMul row (Fin.foldl n (fun acc i => acc * mat i) 1) := by
  intro n
  induction n with
  | zero =>
      intro mat row
      simp only [Fin.foldl_zero]
      exact (Matrix.vecMul_one row).symm
  | succ n ih =>
      intro mat row
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      rw [ih (fun i : Fin n => mat i.castSucc) row]
      exact Matrix.vecMul_vecMul row
        (Fin.foldl n (fun acc i => acc * mat i.castSucc) 1)
        (mat (Fin.last n))

/-- The actual eight-step Magma carry DP is the lower-four distribution
followed by the upper-four transition product. -/
theorem carryDP_eq_half_products (key diff target : Fin 8 → Fin 16) :
    carryDP key diff target =
      Matrix.vecMul (lowerRow key diff target) (upperProduct key diff target) := by
  unfold carryDP lowerRow upperProduct
  rw [foldEight_split]
  exact vecMul_ordered_product 4
    (fun i : Fin 4 => carryMatrix (highIndex i)
      (key (highIndex i)) (diff (highIndex i)) (target (highIndex i)))
    (Fin.foldl 4
      (fun row i => Matrix.vecMul row
        (carryMatrix (lowIndex i)
          (key (lowIndex i)) (diff (lowIndex i)) (target (lowIndex i))))
      initialRow)

/-- Exact factorization of the TRUE eight-step Magma carry path count:
condition on just the two carries across the 16-bit boundary. -/
theorem carryDPCount_eq_half_sum (key diff target : Fin 8 → Fin 16) :
    carryDPCount key diff target =
      ∑ s : CarryState, lowerRow key diff target s * upperCount key diff target s := by
  classical
  unfold carryDPCount
  rw [carryDP_eq_half_products]
  calc
    (∑ t : CarryState,
      Matrix.vecMul (lowerRow key diff target) (upperProduct key diff target) t) =
      ∑ t : CarryState, ∑ s : CarryState,
        lowerRow key diff target s * upperProduct key diff target s t := by
        simp only [Matrix.vecMul_apply_eq_sum]
    _ = ∑ s : CarryState, ∑ t : CarryState,
          lowerRow key diff target s * upperProduct key diff target s t :=
      Finset.sum_comm
    _ = ∑ s : CarryState,
          lowerRow key diff target s * upperCount key diff target s := by
      simp only [upperCount, Finset.mul_sum]

/-- MAIN THEOREM. For all 32-bit round keys and both XOR differences,
the genuine Magma DDT is a FOUR-term sum of two 16-bit carry-block
counts. The output is written as `rot11 target`, to align the nibbles
with the S-box output before rotation. -/
theorem xorDDT_g_eq_four_carry_halves (k inputDiff target : Word) :
    xorDDT_g k inputDiff (rot11 target) =
      ∑ s : CarryState,
        lowerRow (wordDigits k) (wordDigits inputDiff) (wordDigits target) s *
          upperCount (wordDigits k) (wordDigits inputDiff) (wordDigits target) s := by
  rw [xorDDT_g_eq_carryMatrixCount,
      ← carryDPCount_eq_carryMatrixCount]
  exact carryDPCount_eq_half_sum (wordDigits k) (wordDigits inputDiff) (wordDigits target)

/-- The original DDT may also be written with any output difference,
using the inverse rotation to form the target nibble digits. -/
theorem xorDDT_g_eq_four_carry_halves_of_rotate
    (k inputDiff outputDiff target : Word)
    (hrot : rot11 target = outputDiff) :
    xorDDT_g k inputDiff outputDiff =
      ∑ s : CarryState,
        lowerRow (wordDigits k) (wordDigits inputDiff) (wordDigits target) s *
          upperCount (wordDigits k) (wordDigits inputDiff) (wordDigits target) s := by
  subst outputDiff
  exact xorDDT_g_eq_four_carry_halves k inputDiff target

end Magma.DiffanGCarryHalfSplit
