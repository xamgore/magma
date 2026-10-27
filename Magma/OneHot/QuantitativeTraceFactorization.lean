module

public import Magma.OneHot.LinearPrefixMass
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Quantitative factorization of the five-plus-one-plus-two carry trace

A finite equivalence splits every eight-digit input assignment into its
five-digit prefix, active digit, and two-digit suffix. Trace acceptance
depends only on the arithmetic prefix carry and active transition. Summing
over the free suffixes contributes `2^8`, and positional encoding identifies
the prefix sum with the factorized counting model.

This proves `OneHotCountFactorization` and gives unconditional affine formulae
for the original round-function DDT and total three-round column mass at
bits 20 through 23. The proof rearranges finite sums symbolically, without
enumerating twenty-bit prefixes or full words.
-/

open scoped BigOperators

namespace Magma.OneHotQuantitativeTraceFactorization

open Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.OneHotTraceSplit5
open Magma.OneHotPrefixArithmeticBridge
open Magma.OneHotExactColumnMass
open Magma.OneHotLinearPrefixMass
open Magma.OneHotKeyClasses
open Magma.OneHotThreeRoundColumns

private abbrev B : Nat :=
  2 ^ 20

private abbrev Prefix :=
  Fin 5 → Fin 16

private abbrev Suffix :=
  Fin 2 → Fin 16

private abbrev Digits :=
  Fin 8 → Fin 16

/-! ## 1. A symbolic, cardinality-preserving digit decomposition. -/

/-- Split a sequence of eight digits as (five, active, two). -/
private def splitDigits : Digits ≃ (Prefix × Fin 16) × Suffix :=
  ((Fin.appendEquiv 6 2).symm).trans
    ((Fin.succFunEquiv (Fin 16) 5).prodCongr (Equiv.refl Suffix))

/-- Glue a five-digit prefix, the active digit and two suffix digits. -/
private def assemble (p : Prefix) (a : Fin 16) (s : Suffix) : Digits :=
  splitDigits.symm ((p, a), s)

private theorem assemble_0 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 0 = p 0 := by rfl

private theorem assemble_1 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 1 = p 1 := by rfl

private theorem assemble_2 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 2 = p 2 := by rfl

private theorem assemble_3 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 3 = p 3 := by rfl

private theorem assemble_4 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 4 = p 4 := by rfl

private theorem assemble_5 (p : Prefix) (a : Fin 16) (s : Suffix) : assemble p a s 5 = a := by rfl

/-- Rearrange 16^8 digit assignments as 16^5 * 16 * 16^2, symbolically. -/
private theorem sum_eight_as_5_1_2 (f : Digits → Nat) :
    (∑ input : Digits, f input) =
      ∑ p : Prefix, ∑ a : Fin 16, ∑ s : Suffix, f (assemble p a s) := by
  calc
    (∑ input : Digits, f input) =
        ∑ z : (Prefix × Fin 16) × Suffix,
          f (splitDigits.symm z) := by
      exact (Equiv.sum_comp splitDigits.symm f).symm
    _ = ∑ p : Prefix, ∑ a : Fin 16, ∑ s : Suffix,
          f (assemble p a s) := by
      simp only [Fintype.sum_prod_type, assemble]

/-! ## 2. The first five digits are counted by their arithmetic carry. -/

private def preStream (p : Prefix) (n : Nat) : Fin 16 :=
  if h : n < 5 then p ⟨n, h⟩ else 0

/-- The prefix carry depends only on the first five input digits. -/
private def prefixCarryDigits (k : V 32) (p : Prefix) : Fin 2 :=
  lowCarry5 (wordDigits k) (assemble p 0 (fun _ => 0))

private theorem lowCarry5_assemble (k : V 32) (p : Prefix) (a : Fin 16) (s : Suffix) :
    lowCarry5 (wordDigits k) (assemble p a s) = prefixCarryDigits k p := by
  simp only [prefixCarryDigits, lowCarry5, assemble_0, assemble_1, assemble_2, assemble_3,
    assemble_4]

private theorem prefixCarryDigits_eq_incoming (k : V 32) (p : Prefix) :
    prefixCarryDigits k p = incomingCarry (preStream p) (wordDigitStream k) 5 := by
  simp only [prefixCarryDigits, lowCarry5, incomingCarry, ← wordDigitStream_at, assemble_0,
    assemble_1, assemble_2, assemble_3, assemble_4]
  rfl

/-- The library's positional encoding of five digits is the sum used by
    `digitPrefixValue`; only five coefficients are expanded. -/
private theorem prefixValue_eq_encoding (p : Prefix) :
    digitPrefixValue (preStream p) 5 = (finFunctionFinEquiv p).val := by
  rw [finFunctionFinEquiv_apply_val]
  simp [digitPrefixValue, preStream, Fin.sum_univ_five]

/-- All five prefix carries equal ordinary integer addition modulo 2^20.
    No one-million-element enumeration is present in this proof. -/
private theorem prefixCarryDigits_arithmetic (k : V 32) (p : Prefix) :
    (prefixCarryDigits k p).val =
      ((finFunctionFinEquiv p).val + k.toNat % B) / B := by
  have hsum := digitPrefixValue_add_carry
    (preStream p) (wordDigitStream k) 5
  have hout := digitPrefixValue_lt
    (addedDigits (preStream p) (wordDigitStream k)) 5
  rw [prefixValue_eq_encoding, digitPrefixValue_wordDigitStream] at hsum
  have hbase : (16 : Nat) ^ 5 = B := by norm_num [B]
  simp only [hbase] at hsum hout
  rw [prefixCarryDigits_eq_incoming]
  change (incomingCarry (preStream p) (wordDigitStream k) 5).val = _
  change (finFunctionFinEquiv p).val + k.toNat % B =
    digitPrefixValue (addedDigits (preStream p) (wordDigitStream k)) 5 +
      B * (incomingCarry (preStream p) (wordDigitStream k) 5).val at hsum
  dsimp only [B] at hsum hout ⊢
  omega

/-- A digit-prefix sum of local active multiplicities is exactly the
    integer-prefix sum defined in the previously proved affine model. -/
private theorem sum_prefix_multiplicity (k : V 32) (q : Fin 16)
    (r : Fin 4) :
    (∑ p : Prefix, activeMultiplicity q (prefixCarryDigits k p) r) =
      prefixWeightedActiveCount (k.toNat % B) q r := by
  have hpoint (p : Prefix) :
      activeMultiplicity q (prefixCarryDigits k p) r =
        if prefixCarry (k.toNat % B) (finFunctionFinEquiv p).val = 0
        then activeMultiplicity q 0 r else activeMultiplicity q 1 r := by
    have hcarry := prefixCarryDigits_arithmetic k p
    change (prefixCarryDigits k p).val =
      prefixCarry (k.toNat % B) (finFunctionFinEquiv p).val at hcarry
    by_cases hz : prefixCarryDigits k p = 0
    · have hzero : prefixCarry (k.toNat % B)
          (finFunctionFinEquiv p).val = 0 := by
        rw [← hcarry, hz]
        rfl
      simp [hz, hzero]
    · have hone : prefixCarryDigits k p = 1 := by
        apply Fin.ext
        have hb := (prefixCarryDigits k p).isLt
        have hn : (prefixCarryDigits k p).val ≠ 0 := by
          intro heq
          apply hz
          exact Fin.ext heq
        omega
      have hnonzero : prefixCarry (k.toNat % B)
          (finFunctionFinEquiv p).val ≠ 0 := by
        rw [← hcarry, hone]
        decide
      simp [hone, hnonzero]
  calc
    (∑ p : Prefix, activeMultiplicity q (prefixCarryDigits k p) r) =
        ∑ p : Prefix,
          if prefixCarry (k.toNat % B) (finFunctionFinEquiv p).val = 0
          then activeMultiplicity q 0 r else activeMultiplicity q 1 r := by
      apply Finset.sum_congr rfl
      intro p _
      exact hpoint p
    _ = ∑ x : Fin (16 ^ 5),
          if prefixCarry (k.toNat % B) x.val = 0
          then activeMultiplicity q 0 r else activeMultiplicity q 1 r := by
      apply Fintype.sum_equiv finFunctionFinEquiv
      intro p
      rfl
    _ = ∑ x : Fin B,
          if prefixCarry (k.toNat % B) x.val = 0
          then activeMultiplicity q 0 r else activeMultiplicity q 1 r := by
      exact Fintype.sum_equiv (finCongr (by norm_num [B])) _ _ (fun _ => rfl)
    _ = prefixWeightedActiveCount (k.toNat % B) q r := by
      unfold prefixWeightedActiveCount
      rw [Finset.sum_range]

/-! ## 3. Trace acceptance depends only on prefix and active digit. -/

private abbrev activeSuccess (q : Fin 16) (c : Fin 2) (r : Fin 4) (a : Fin 16) : Prop :=
  (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).1 = 2 ∧
    (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.1 =
      (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) a (c, c)).2.2

private theorem activeMultiplicity_eq_sum (q : Fin 16) (c : Fin 2) (r : Fin 4) :
    activeMultiplicity q c r = ∑ a : Fin 16, if activeSuccess q c r a then 1 else 0 := by
  unfold activeMultiplicity activeSuccess
  rw [Finset.card_filter]

private theorem assemble_trace_iff_active (k : V 32) (r : Fin 4) (p : Prefix) (a : Fin 16)
    (s : Suffix) :
    (carryTrace (wordDigits k) (oneHotDiffDigits r) oneHotTargetDigits (assemble p a s)).2 = true ↔
      activeSuccess (keyNibble5 k) (prefixCarryDigits k p) r a := by
  have hp := tracePrefix5_eq_lowCarry5 (wordDigits k) (assemble p a s) r
  rw [lowCarry5_assemble] at hp
  have htrace :=
    oneHot_trace_iff_active (wordDigits k) (assemble p a s) r (prefixCarryDigits k p) hp
  simpa only [activeSuccess, assemble_5, ← keyNibble5_eq_wordDigits] using htrace

/-- Original eight-digit DP equals its semantic accepted-trace count.
    This applies the already proved counting theorem, not computation. -/
private theorem dp_eq_eight_digit_sum (k : V 32) (r : Fin 4) :
    oneHotDPCount k (⟨20 + r.val, by omega⟩ : Fin 32) =
      ∑ input : Digits,
        if (carryTrace (wordDigits k)
          (oneHotDiffDigits r) oneHotTargetDigits input).2 = true
        then (1 : Nat) else 0 := by
  let j : Fin 32 := ⟨20 + r.val, by omega⟩
  change carryDPCount (wordDigits k) (wordDigits (bitOutput j))
    oneHotTargetDigits = _
  rw [← wordDigits_oneHot_output]
  rw [← carryWordCount_eq_carryDPCount]
  rw [carryWordCount_eq_digitAssignments, Finset.card_filter]
  change (∑ input : Digits,
    if (carryTrace (wordDigits k) (wordDigits (bitOutput j))
        (wordDigits (0x00200000#32)) input).2 = true
    then (1 : Nat) else 0) = _
  rw [show bitOutput j = BitVec.ofNat 32 (2 ^ (20 + r.val)) from rfl,
      wordDigits_oneHot_input, wordDigits_oneHot_output]

/-- There are 16^2 = 2^8 irrelevant, always-admissible suffixes. -/
private theorem sum_suffix_constant (q : Fin 16) (c : Fin 2)
    (r : Fin 4) (a : Fin 16) :
    (∑ _s : Suffix,
      if activeSuccess q c r a then (1 : Nat) else 0) =
      2 ^ 8 * (if activeSuccess q c r a then (1 : Nat) else 0) := by
  have hc : Fintype.card Suffix = 2 ^ 8 := by
    norm_num [Fintype.card_fun]
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, hc]

/-! ## 4. Quantitative theorem, no certificate premise. -/

/-- The previously open quantitative identity: the real eight-digit DP
    is EXACTLY the factorized prefix/active/suffix count. -/
theorem oneHotDPCount_eq_factorized (k : V 32) (r : Fin 4) :
    oneHotDPCount k (⟨20 + r.val, by omega⟩ : Fin 32) =
      factorizedOneHotCount k r := by
  calc
    oneHotDPCount k (⟨20 + r.val, by omega⟩ : Fin 32) =
        ∑ input : Digits,
          if (carryTrace (wordDigits k) (oneHotDiffDigits r)
            oneHotTargetDigits input).2 = true then (1 : Nat) else 0 :=
      dp_eq_eight_digit_sum k r
    _ = ∑ p : Prefix, ∑ a : Fin 16, ∑ s : Suffix,
          if activeSuccess (keyNibble5 k) (prefixCarryDigits k p) r a
          then (1 : Nat) else 0 := by
      rw [sum_eight_as_5_1_2]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro s _
      simp only [assemble_trace_iff_active]
    _ = ∑ p : Prefix, ∑ a : Fin 16,
          2 ^ 8 *
            (if activeSuccess (keyNibble5 k) (prefixCarryDigits k p) r a
            then (1 : Nat) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro a _
      exact sum_suffix_constant _ _ _ _
    _ = 2 ^ 8 *
          (∑ p : Prefix, activeMultiplicity
            (keyNibble5 k) (prefixCarryDigits k p) r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [activeMultiplicity_eq_sum, Finset.mul_sum]
    _ = factorizedOneHotCount k r := by
      rw [sum_prefix_multiplicity]
      rfl

/-- THE missing proposition from the preceding module is proved. -/
theorem oneHotCountFactorization_proved : OneHotCountFactorization := by
  intro k r
  exact oneHotDPCount_eq_factorized k r

/-- Unconditional exact single-round DDT for EVERY key, not just the
    previously computed keys 1 and 2. -/
theorem oneHot_g_DDT_affine (k : V 32) (r : Fin 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) =
      2 ^ 8 *
        ((B - k.toNat % B) * activeMultiplicity (keyNibble5 k) 0 r +
         (k.toNat % B) * activeMultiplicity (keyNibble5 k) 1 r) :=
  oneHot_g_DDT_affine_of_factorization oneHotCountFactorization_proved k r

/-- Unconditional exact aggregate mass of a three-round one-hot column. -/
theorem oneHot_three_round_column_mass_affine
    (k₀ k₁ k₂ : V 32) (r : Fin 4) :
    (∑ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32,
          bitOutput (⟨20 + r.val, by omega⟩ : Fin 32))) =
      2 ^ 32 * (2 ^ 8 *
        ((B - k₁.toNat % B) * activeMultiplicity (keyNibble5 k₁) 0 r +
         (k₁.toNat % B) * activeMultiplicity (keyNibble5 k₁) 1 r)) :=
  oneHot_three_round_column_mass_affine_of_factorization
    oneHotCountFactorization_proved k₀ k₁ k₂ r

end Magma.OneHotQuantitativeTraceFactorization
