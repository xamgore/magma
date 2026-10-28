module

public import Magma.TwoHot.OutputOneSevenExactCounts
import Mathlib.Tactic.Ring
import all Init.Data.Range.Basic
import Magma.TwoHot.OutputOneSevenExactCounts

@[expose] public section

/-!
A uniform, exact LOCAL two-digit counting model for all seven two-hot
input differences with output XOR difference 1.

INSTALL AFTER:
  Magma.TwoHot.OutputOneSevenExactCounts

This is a symbolic normalization of the PREVIOUSLY defined
`weightedSevenCount` (six same-nibble cases, one cross-nibble case).
It does NOT yet prove its equality to `carryDPCount` for every key.

The normalized formula is

  16 * ((16^5 - K) * twoDigitMultiplicity(k,p,0) +
                      K  * twoDigitMultiplicity(k,p,1)).

For the six same-nibble pairs, `twoDigitMultiplicity = 16*localFiveCount`
because the sixth digit is free.  For (23,24), it equals
`localFiveSixCount` because both digits are constrained.  This enables
ONE trace-factorization proof for all seven pairs rather than two.

No sorry / native_decide / custom axioms. No full-DP execution.
-/

namespace Magma.TwoHotUniformTwoDigitKernel

open Magma
open Magma.CarryAutomaton
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotOutputOneSevenLocal
open Magma.TwoHotOutputOneSevenExactCounts

private abbrev Word :=
  V 32

private abbrev PairBits :=
  Fin 32 × Fin 32

private abbrev Digit :=
  Fin 16

private abbrev Carry :=
  Fin 2

/-- The unique two-nibble case among the seven candidate pairs. -/
def crossPair : PairBits := (23, 24)

/-- One predicate for the full local two-digit behavior.
    For the six pairs within digit 5, digit 6 is unrestricted.
    For (23,24) we require output 0 in digit 6 and rejoining of carries
    before the free final digit 7. -/
def twoDigitSuccess (k : Word) (p : PairBits)
    (c : Carry) (x5 x6 : Digit) : Prop :=
  let q5 := wordDigits k (5 : Fin 8)
  let delta5 := wordDigits (twoHot p.1 p.2) (5 : Fin 8)
  let st5 := sboxCarryStep (5 : Fin 8) q5 delta5 x5 (c,c)
  if p = crossPair then
    let st6 := sboxCarryStep (6 : Fin 8)
      (wordDigits k (6 : Fin 8)) 1 x6 st5.2
    st5.1 = 2 ∧ st6.1 = 0 ∧ st6.2.1 = st6.2.2
  else
    st5.1 = 2 ∧ st5.2.1 = st5.2.2

instance (k : Word) (p : PairBits) (c : Carry) (x5 x6 : Digit) :
    Decidable (twoDigitSuccess k p c x5 x6) := by
  unfold twoDigitSuccess
  split <;> infer_instance

/-- Exactly 16² local assignments are considered for each incoming carry. -/
def twoDigitMultiplicity (k : Word) (p : PairBits) (c : Carry) : Nat :=
  ∑ x5 : Digit, ∑ x6 : Digit,
    if twoDigitSuccess k p c x5 x6 then (1 : Nat) else 0

/-- The exceptional pair uses EXACTLY the earlier two-digit count. -/
theorem twoDigitMultiplicity_cross (k : Word) (c : Carry) :
    twoDigitMultiplicity k crossPair c =
      localFiveSixCount (wordDigits k (5 : Fin 8))
        (wordDigits k (6 : Fin 8)) c := by
  -- Only closed nibble extraction of the fixed difference 2^23 xor 2^24.
  have hdelta : wordDigits (twoHot (23 : Fin 32) (24 : Fin 32))
      (5 : Fin 8) = (8 : Fin 16) := by decide +kernel
  simp only [twoDigitMultiplicity, twoDigitSuccess, crossPair,
    ite_true, hdelta]
  rfl

/-- In the six same-nibble cases, x6 is completely free, giving exactly
    sixteen copies of the existing single-digit local count. -/
theorem twoDigitMultiplicity_same (k : Word) (p : PairBits) (c : Carry)
    (hp : p ≠ crossPair) :
    twoDigitMultiplicity k p c =
      16 * localFiveCount (wordDigits k (5 : Fin 8))
        (wordDigits (twoHot p.1 p.2) (5 : Fin 8)) c := by
  simp only [twoDigitMultiplicity, twoDigitSuccess, ite_eq_right hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [show localFiveCount (wordDigits k (5 : Fin 8))
      (wordDigits (twoHot p.1 p.2) (5 : Fin 8)) c =
      ∑ x : Digit,
        if (let step := sboxCarryStep (5 : Fin 8)
               (wordDigits k (5 : Fin 8))
               (wordDigits (twoHot p.1 p.2) (5 : Fin 8)) x (c,c)
            step.1 = 2 ∧ step.2.1 = step.2.2)
        then (1 : Nat) else 0 from by
          unfold localFiveCount
          rw [Finset.card_filter]]
  rw [Finset.mul_sum]

/-! ### Symbolic input decomposition: 5 prefix, 2 local, 1 free digit. -/

private abbrev Prefix :=
  Fin 5 → Digit

private abbrev Middle :=
  Fin 2 → Digit

private abbrev Suffix :=
  Fin 1 → Digit

private abbrev Digits :=
  Fin 8 → Digit

/-- Exact digit-level bijection. Not an enumeration of 32-bit words. -/
def splitEight : Digits ≃ (Prefix × Middle) × Suffix :=
  ((Fin.appendEquiv 7 1).symm).trans
    ((Fin.appendEquiv 5 2).symm.prodCongr (Equiv.refl Suffix))

/-- All full assignments split uniquely into their lower five digits,
    two locally relevant digits, and one free upper digit. -/
theorem sumEight_as_prefix_middle_suffix (f : Digits → Nat) :
    (∑ x : Digits, f x) =
      ∑ p : Prefix, ∑ mid : Middle, ∑ u : Suffix,
        f (splitEight.symm ((p, mid), u)) := by
  calc
    (∑ x : Digits, f x) =
        ∑ z : (Prefix × Middle) × Suffix, f (splitEight.symm z) := by
      exact (Equiv.sum_comp splitEight.symm f).symm
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- The same prefix-weighted count, now uniformly using TWO active
    nibble positions and one free high nibble. -/
def uniformSevenCount (k : Word) (p : PairBits) : Nat :=
  let K := prefixK k
  16 * ((16^5-K) * twoDigitMultiplicity k p 0 +
                   K * twoDigitMultiplicity k p 1)

/-- No extra hypothesis: this is a symbolic refactor of the previously
    independently tested formula. It does NOT claim DP equivalence. -/
theorem uniformSevenCount_eq_weightedSevenCount (k : Word) (p : PairBits) :
    uniformSevenCount k p = weightedSevenCount k p := by
  by_cases hp : p = crossPair
  · subst p
    dsimp only [uniformSevenCount, weightedSevenCount]
    rw [ite_eq_left (show crossPair = ((23 : Fin 32), (24 : Fin 32)) from rfl),
      twoDigitMultiplicity_cross, twoDigitMultiplicity_cross]
  · dsimp only [uniformSevenCount, weightedSevenCount]
    rw [ite_eq_right (show p ≠ ((23 : Fin 32), (24 : Fin 32)) from hp)]
    rw [twoDigitMultiplicity_same k p 0 hp,
        twoDigitMultiplicity_same k p 1 hp]
    ring

/-- The original seven-weight bridge can now be targeted through ONE
    uniform local kernel. This is a logical reduction, not a new axiom. -/
theorem sevenWeightFiberBridge_of_uniform
    (h : ∀ (k : Word) (p : PairBits), p ∈ sevenPairs →
      carryDPCount (wordDigits k) (wordDigits (twoHot p.1 p.2))
        (wordDigits (0x00200000#32)) = uniformSevenCount k p) :
    sevenWeightFiberBridge := by
  intro k p hp
  calc
    carryDPCount (wordDigits k) (wordDigits (twoHot p.1 p.2))
        (wordDigits (0x00200000#32)) = uniformSevenCount k p := h k p hp
    _ = weightedSevenCount k p := uniformSevenCount_eq_weightedSevenCount k p

end Magma.TwoHotUniformTwoDigitKernel
