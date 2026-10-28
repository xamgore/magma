module

public import Magma.TwoHot.SevenTraceKernelBridge
public import Magma.OneHot.QuantitativeTraceFactorization
public import Magma.OneHot.LinearPrefixMass
import all Init.Data.Range.Basic

@[expose] public section

/-!
Seven exact two-hot coefficients for output XOR difference 1:
final quantitative bridge, using the already proved pointwise trace theorem.

No 2^32 enumerations, no new trusted computations, no sorry, no native_decide.
-/

open scoped BigOperators

namespace Magma.TwoHotSevenQuantitativeClosure

open Magma
open Magma.CarryAutomaton
open Magma.OneHotPrefixArithmeticBridge
open Magma.OneHotLinearPrefixMass
open Magma.OneHotQuantitativeTraceFactorization
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotOutputOneSevenSoundness
open Magma.TwoHotOutputOneSevenExactCounts
open Magma.TwoHotUniformTwoDigitKernel
open Magma.TwoHotSevenTraceKernelBridge

private abbrev Word :=
  V 32

private abbrev Digit :=
  Fin 16

private abbrev Prefix :=
  Fin 5 → Digit

private abbrev Middle :=
  Fin 2 → Digit

private abbrev Suffix :=
  Fin 1 → Digit

private abbrev Digits :=
  Fin 8 → Digit

private abbrev PairBits :=
  Fin 32 × Fin 32

private abbrev B : Nat :=
  16 ^ 5

/-- The two middle digits, in their natural order. -/
private def middleEquiv : Middle ≃ Digit × Digit where
  toFun d := (d 0, d 1)
  invFun xy := fun i => if i = 0 then xy.1 else xy.2
  left_inv := by
    intro d
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro xy
    rcases xy with ⟨x,y⟩
    simp

/-- A sum over two middle digits is exactly a nested local sum. -/
private theorem middle_sum (f : Digit → Digit → Nat) :
    (∑ mid : Middle, f (mid 0) (mid 1)) =
      ∑ x5 : Digit, ∑ x6 : Digit, f x5 x6 := by
  calc
    (∑ mid : Middle, f (mid 0) (mid 1)) =
        ∑ xy : Digit × Digit, f xy.1 xy.2 := by
      apply Fintype.sum_equiv middleEquiv
      intro mid
      rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Sum over the free final nibble is exactly multiplication by 16. -/
private theorem free_suffix_sum (n : Nat) :
    (∑ _s : Suffix, n) = 16 * n := by
  simp [Suffix, Finset.sum_const]

/-- The five low digits of `splitEight` are exactly the prefix. -/
private theorem assembled_low (pre : Prefix) (mid : Middle) (u : Suffix)
    (i : Fin 5) :
    (splitEight.symm ((pre, mid), u)) (i.castLE (by decide : 5 ≤ 8)) = pre i := by
  fin_cases i <;> rfl

private theorem assembled_middle5 (pre : Prefix) (mid : Middle) (u : Suffix) :
    (splitEight.symm ((pre, mid), u)) 5 = mid 0 := by rfl

private theorem assembled_middle6 (pre : Prefix) (mid : Middle) (u : Suffix) :
    (splitEight.symm ((pre, mid), u)) 6 = mid 1 := by rfl

/-- The previously proved prefix carry is unaffected by the two active
    input digits and the completely free last digit. -/
private theorem lowCarry5_split (k : Word) (pre : Prefix)
    (mid : Middle) (u : Suffix) :
    lowCarry5 (wordDigits k) (splitEight.symm ((pre, mid), u)) =
      prefixCarryDigits k pre := by
  simp only [lowCarry5, prefixCarryDigits]
  rw [show (splitEight.symm ((pre, mid), u)) 0 = pre 0 from rfl,
      show (splitEight.symm ((pre, mid), u)) 1 = pre 1 from rfl,
      show (splitEight.symm ((pre, mid), u)) 2 = pre 2 from rfl,
      show (splitEight.symm ((pre, mid), u)) 3 = pre 3 from rfl,
      show (splitEight.symm ((pre, mid), u)) 4 = pre 4 from rfl]
  rfl

/-- Arithmetic form of the publicized, already proved prefix lemma. -/
private theorem prefixCarryDigits_value (k : Word) (pre : Prefix) :
    (prefixCarryDigits k pre).val =
      ((finFunctionFinEquiv pre).val + prefixK k) / B := by
  have h := prefixCarryDigits_arithmetic k pre
  change (prefixCarryDigits k pre).val =
    ((finFunctionFinEquiv pre).val + k.toNat % (2 ^ 20)) / (2 ^ 20) at h
  norm_num [prefixK, B] at h ⊢
  exact h

/-- A purely elementary generic weighted-prefix lemma. It makes no
    assumption about the shape of the local multiplicities. -/
private theorem prefix_sum_by_carry (k : Word) (f : Fin 2 → Nat) :
    (∑ pre : Prefix, f (prefixCarryDigits k pre)) =
      (B - prefixK k) * f 0 + prefixK k * f 1 := by
  let K := prefixK k
  have hK : K < B := by
    dsimp [K, prefixK, B]
    exact Nat.mod_lt _ (by norm_num)
  have hpoint (pre : Prefix) :
      f (prefixCarryDigits k pre) =
        if prefixCarry K (finFunctionFinEquiv pre).val = 0
        then f 0 else f 1 := by
    have hc := prefixCarryDigits_value k pre
    change (prefixCarryDigits k pre).val =
      prefixCarry K (finFunctionFinEquiv pre).val at hc
    by_cases hz : prefixCarry K (finFunctionFinEquiv pre).val = 0
    · have hzero : prefixCarryDigits k pre = 0 := Fin.ext (by omega)
      simp [hz, hzero]
    · have hone : prefixCarryDigits k pre = 1 := by
        apply Fin.ext
        have hb := (prefixCarryDigits k pre).isLt
        omega
      simp [hz, hone]
  calc
    (∑ pre : Prefix, f (prefixCarryDigits k pre)) =
        ∑ pre : Prefix,
          if prefixCarry K (finFunctionFinEquiv pre).val = 0
          then f 0 else f 1 := by
      apply Finset.sum_congr rfl
      intro pre _
      exact hpoint pre
    _ = ∑ x : Fin (16 ^ 5),
          if prefixCarry K x.val = 0 then f 0 else f 1 := by
      apply Fintype.sum_equiv finFunctionFinEquiv
      intro pre
      rfl
    _ = ∑ x : Fin B,
          if prefixCarry K x.val = 0 then f 0 else f 1 := by
      exact Fintype.sum_equiv (finCongr (by norm_num [B])) _ _ (fun _ => rfl)
    _ = ∑ x ∈ Finset.range B,
          if prefixCarry K x = 0 then f 0 else f 1 := by
      rw [Finset.sum_range]
    _ = (B - K) * f 0 + K * f 1 := by
      have hzero := prefixCarry_zero_count K hK
      have hone := prefixCarry_one_count K hK
      change ((Finset.range (2 ^ 20)).filter (fun x => prefixCarry K x = 0)).card =
        2 ^ 20 - K at hzero
      change ((Finset.range (2 ^ 20)).filter (fun x => prefixCarry K x = 1)).card =
        K at hone
      have hbase : (2 : Nat) ^ 20 = B := by norm_num [B]
      rw [hbase] at hzero hone
      have hfilter :
          (Finset.range B).filter (fun x => ¬prefixCarry K x = 0) =
            (Finset.range B).filter (fun x => prefixCarry K x = 1) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hx, hn⟩
          exact ⟨hx, (prefixCarry_one_iff K x hK hx).mpr
            (by have := (prefixCarry_zero_iff K x hK hx); omega)⟩
        · rintro ⟨hx, h1⟩
          exact ⟨hx, by rw [h1]; decide⟩
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hzero, hfilter, hone]
      simp only [Nat.cast_id]

/-- The finite eight-digit kernel sum is exactly the uniform closed
    two-digit weight. No DDT enumeration or reduction of a large DP. -/
theorem kernel_sum_eq_uniformSevenCount (k : Word) (p : PairBits) :
    (∑ input : Digits,
       if twoDigitSuccess k p (lowCarry5 (wordDigits k) input)
         (input 5) (input 6) then (1 : Nat) else 0) =
      uniformSevenCount k p := by
  rw [sumEight_as_prefix_middle_suffix]
  have hmiddle (c : Fin 2) :
      (∑ mid : Middle,
        if twoDigitSuccess k p c (mid 0) (mid 1) then (1 : Nat) else 0) =
      twoDigitMultiplicity k p c := by
    exact middle_sum (fun x5 x6 =>
      if twoDigitSuccess k p c x5 x6 then (1 : Nat) else 0)
  have hprefix (pre : Prefix) :
      (∑ mid : Middle, ∑ u : Suffix,
          if twoDigitSuccess k p
            (lowCarry5 (wordDigits k) (splitEight.symm ((pre, mid), u)))
            ((splitEight.symm ((pre, mid), u)) 5)
            ((splitEight.symm ((pre, mid), u)) 6)
          then (1 : Nat) else 0) =
        16 * twoDigitMultiplicity k p (prefixCarryDigits k pre) := by
    simp_rw [lowCarry5_split, assembled_middle5, assembled_middle6]
    simp only [free_suffix_sum]
    rw [← Finset.mul_sum]
    rw [hmiddle]
  calc
    (∑ pre : Prefix, ∑ mid : Middle, ∑ u : Suffix,
        if twoDigitSuccess k p
          (lowCarry5 (wordDigits k) (splitEight.symm ((pre, mid), u)))
          ((splitEight.symm ((pre, mid), u)) 5)
          ((splitEight.symm ((pre, mid), u)) 6)
        then (1 : Nat) else 0) =
      ∑ pre : Prefix,
        16 * twoDigitMultiplicity k p (prefixCarryDigits k pre) := by
      apply Finset.sum_congr rfl
      intro pre _
      exact hprefix pre
    _ = 16 * ∑ pre : Prefix,
          twoDigitMultiplicity k p (prefixCarryDigits k pre) := by
      rw [Finset.mul_sum]
    _ = uniformSevenCount k p := by
      rw [prefix_sum_by_carry]
      rfl

/-- The missing unconditional numerical equality between the genuine
    eight-step carry DP and the closed seven-pair formula. -/
theorem sevenWeightFiberBridge_proved : sevenWeightFiberBridge := by
  intro k p hp
  calc
    carryDPCount (wordDigits k) (wordDigits (twoHot p.1 p.2))
        (wordDigits (0x00200000#32)) =
      ∑ input : Digits,
        if twoDigitSuccess k p (lowCarry5 (wordDigits k) input)
          (input 5) (input 6) then (1 : Nat) else 0 := by
      exact carryDP_eq_twoDigit_kernel_sum k p hp
    _ = uniformSevenCount k p := kernel_sum_eq_uniformSevenCount k p
    _ = weightedSevenCount k p := uniformSevenCount_eq_weightedSevenCount k p

/-- The completed exact DDT formula for ALL strictly ordered two-hot
    input differences (the 489 excluded differences have value zero). -/
theorem all_496_twoHot_exact (k : Word) (p : PairBits)
    (hij : p.1.val < p.2.val) :
    xorDDT_g k (twoHot p.1 p.2) (1#32) =
      proposedTwoHotClosedCount k p := by
  exact ordered_twoHot_closed_of_fiber_bridge
    sevenWeightFiberBridge_proved k p hij

end Magma.TwoHotSevenQuantitativeClosure
