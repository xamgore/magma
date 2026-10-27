module

public import Magma.OneHot.ExactLocalSupportCompleteness
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Key classes attaining the 72-cell support maximum

Exact finite local scores characterize equality in the sharp fixed-key
support bound. Fourteen admissible three-nibble prefixes combine with
independent restrictions on the five remaining key digits.

`support_eq_72_iff_key_class` gives necessary and sufficient conditions
on actual round keys. The maximizing coordinate space has cardinality
2016; transporting that count to the set of `BitVec 32` keys is a separate
cardinality statement. No full key-space enumeration is used.
-/

namespace Magma.OneHotSupport72KeyClasses

open Magma
open Magma.CarryAutomaton
open Magma.OneHotFixedKeySupportAudit
open Magma.OneHotFixedKeySupport72
open Magma.OneHotExactCarryRegimes
open Magma.OneHotExactLocalSupportCompleteness

private abbrev Word :=
  V 32

private abbrev Q :=
  Fin 16

/-! ## 1. Five exact score lookup arrays for the first 3 nibbles. -/

private def score0 (q : Q) : Nat :=
  ([10, 8, 9, 7, 8, 5, 8, 7, 7, 7, 8, 6, 7, 4, 7, 8] : List Nat).getD q.val 0

private def score1No (q : Q) : Nat :=
  ([8, 7, 7, 7, 7, 4, 5, 4, 6, 5, 5, 5, 7, 6, 7, 6] : List Nat).getD q.val 0

private def score1Yes (q : Q) : Nat :=
  ([8, 8, 8, 8, 7, 6, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8] : List Nat).getD q.val 0

private def score2No (q : Q) : Nat :=
  ([8, 7, 5, 3, 3, 4, 4, 5, 7, 6, 5, 4, 4, 5, 5, 6] : List Nat).getD q.val 0

private def score2Yes (q : Q) : Nat :=
  ([9, 7, 6, 4, 5, 5, 6, 7, 8, 7, 6, 5, 6, 6, 7, 8] : List Nat).getD q.val 0

private theorem score0_correct (q : Q) : localPotentialCount (0 : Fin 8) q false = score0 q := by
  revert q
  decide +kernel

private theorem score1No_correct (q : Q) :
    localPotentialCount (1 : Fin 8) q false = score1No q := by
  revert q
  decide +kernel

private theorem score1Yes_correct (q : Q) :
    localPotentialCount (1 : Fin 8) q true = score1Yes q := by
  revert q
  decide +kernel

private theorem score2No_correct (q : Q) :
    localPotentialCount (2 : Fin 8) q false = score2No q := by
  revert q
  decide +kernel

private theorem score2Yes_correct (q : Q) :
    localPotentialCount (2 : Fin 8) q true = score2Yes q := by
  revert q
  decide +kernel

/-- Exact first-three-nibble score with the TRUE prefix carry regime. -/
private def prefix3 (q0 q1 q2 : Q) : Nat :=
  score0 q0 +
    (if q0.val = 0 then score1No q1 else score1Yes q1) +
    (if q0.val = 0 ∧ q1.val = 0 then score2No q2 else score2Yes q2)

def q1WhenQ0Zero : Finset Q :=
  {1, 2, 3, 4, 12, 14}

def q1WhenQ0Two : Finset Q :=
  {0, 1, 2, 3, 12, 13, 14, 15}

/-- The only ways to attain the FIRST-THREE-NIBBLE ceiling 26.
    The all-zero prefix is locally optimal but ultimately cannot supply
    carry one to nibble 3; it is eliminated in the final theorem. -/
theorem prefix3_eq_26_iff (q0 q1 q2 : Q) :
    prefix3 q0 q1 q2 = 26 ↔
      q2 = 0 ∧
        ((q0 = 0 ∧ (q1 = 0 ∨ q1 ∈ q1WhenQ0Zero)) ∨
          (q0 = 2 ∧ q1 ∈ q1WhenQ0Two)) := by
  revert q0 q1 q2
  decide +kernel

/-- The true maximizing FIRST THREE digits, excluding the impossible
    all-zero prefix for the remaining higher-nibble maxima. -/
def goodPrefix3 (q0 q1 q2 : Q) : Prop :=
  q2 = 0 ∧ ((q0 = 0 ∧ q1 ∈ q1WhenQ0Zero) ∨ (q0 = 2 ∧ q1 ∈ q1WhenQ0Two))

instance (q0 q1 q2 : Q) : Decidable (goodPrefix3 q0 q1 q2) := by
  unfold goodPrefix3
  infer_instance

def q3Choices : Finset Q :=
  {0, 12, 13, 14}

def q4Choices : Finset Q :=
  {2}

def q5Choices : Finset Q :=
  {1, 3}

def q6Choices : Finset Q :=
  {6, 14, 15}

def q7Choices : Finset Q :=
  {0, 2, 4, 8, 10, 12}

/-- Exact key conditions, with independent restrictions on the final
    five nibbles. -/
def isMax72Key (k : Word) : Prop :=
  goodPrefix3 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2) ∧
    wordDigits k 3 ∈ q3Choices ∧
    wordDigits k 4 ∈ q4Choices ∧
    wordDigits k 5 ∈ q5Choices ∧
    wordDigits k 6 ∈ q6Choices ∧
    wordDigits k 7 ∈ q7Choices

instance (k : Word) : Decidable (isMax72Key k) := by
  unfold isMax72Key
  infer_instance

/-- Exactly fourteen three-nibble prefixes are compatible with the
    full 72-cell maximum, and not fifteen. This counts only 16^3
    short coordinate triples, not 32-bit keys. -/
def maximizingPrefixTriples : Finset (Q × Q × Q) :=
  (Finset.univ : Finset (Q × Q × Q)).filter
    (fun p : Q × Q × Q => goodPrefix3 p.1 p.2.1 p.2.2)

theorem maximizingPrefixTriples_card : maximizingPrefixTriples.card = 14 := by decide +kernel

/-- Independent high-digit choices: four, one, two, three, six. -/
theorem high_choices_card :
    q3Choices.card = 4 ∧ q4Choices.card = 1 ∧
    q5Choices.card = 2 ∧ q6Choices.card = 3 ∧
    q7Choices.card = 6 := by
  decide +kernel

/-- Purely finite coordinate space of the maximizing keys. Each
    coordinate tuple corresponds to one distinct 32-bit word through
    `wordDigitsEquiv`; that final bijection will be used for a subsequent
    cardinality theorem about actual `BitVec 32` keys. -/
private abbrev HighDigits := Q × (Q × (Q × (Q × Q)))

private def maximizingHighDigits : Finset HighDigits :=
  q3Choices ×ˢ (q4Choices ×ˢ (q5Choices ×ˢ (q6Choices ×ˢ q7Choices)))

def maximizingCoordinateTuples : Finset ((Q × Q × Q) × HighDigits) :=
  maximizingPrefixTriples ×ˢ maximizingHighDigits

/-- The exact count 2016 is now a small symbolic product of six
    *independently checked* finite-set cardinalities. -/
theorem maximizingCoordinateTuples_card :
    maximizingCoordinateTuples.card = 2016 := by
  rcases high_choices_card with ⟨h3,h4,h5,h6,h7⟩
  simp only [maximizingCoordinateTuples, maximizingHighDigits,
    Finset.card_product, maximizingPrefixTriples_card,
    h3,h4,h5,h6,h7]

/-! ## 2. Closed local classifications for the last five digits. -/

private def highCap (i : Fin 8) : Nat :=
  match i.val with
  | 3 => 9
  | 4 => 10
  | 5 => 11
  | 6 => 7
  | 7 => 9
  | _ => 0

/-- Covers both carry regimes. -/
private theorem high_le (i : Fin 8) (q : Q) (flag : Bool)
    (hi : 3 ≤ i.val) :
    localPotentialCount i q flag ≤ highCap i := by
  revert i q flag
  decide +kernel

private theorem high3_eq_iff (q : Q) (flag : Bool) :
    localPotentialCount (3 : Fin 8) q flag = 9 ↔ flag = true ∧ q ∈ q3Choices := by
  revert q flag
  decide +kernel

private theorem high4_eq_iff (q : Q) (flag : Bool) :
    localPotentialCount (4 : Fin 8) q flag = 10 ↔ flag = true ∧ q ∈ q4Choices := by
  revert q flag
  decide +kernel

private theorem high5_eq_iff (q : Q) (flag : Bool) :
    localPotentialCount (5 : Fin 8) q flag = 11 ↔ flag = true ∧ q ∈ q5Choices := by
  revert q flag
  decide +kernel

private theorem high6_eq_iff (q : Q) (flag : Bool) :
    localPotentialCount (6 : Fin 8) q flag = 7 ↔ flag = true ∧ q ∈ q6Choices := by
  revert q flag
  decide +kernel

private theorem high7_eq_iff (q : Q) (flag : Bool) :
    localPotentialCount (7 : Fin 8) q flag = 9 ↔ flag = true ∧ q ∈ q7Choices := by
  revert q flag
  decide +kernel

/-! ## 3. Relate the true carry flags to the first key digits. -/

private theorem digit0_nat (k : Word) : (wordDigits k 0).val = k.toNat % 16 := by
  simpa using wordDigits_val k (0 : Fin 8)

private theorem digit1_nat (k : Word) : (wordDigits k 1).val = k.toNat / 16 % 16 := by
  simpa using wordDigits_val k (1 : Fin 8)

private theorem digit2_nat (k : Word) : (wordDigits k 2).val = k.toNat / 256 % 16 := by
  simpa using wordDigits_val k (2 : Fin 8)

private theorem flag0 (k : Word) : exactCarryFlag k 0 = false := by
  simp [exactCarryFlag, nibbleBase, Nat.mod_one]

private theorem flag1 (k : Word) : exactCarryFlag k 1 = decide ((wordDigits k 0).val ≠ 0) := by
  have h := digit0_nat k
  change decide (k.toNat % 16 ≠ 0) = decide ((wordDigits k 0).val ≠ 0)
  rw [h]

private theorem flag2 (k : Word) :
    exactCarryFlag k 2 = decide ((wordDigits k 0).val ≠ 0 ∨ (wordDigits k 1).val ≠ 0) := by
  have h0 := digit0_nat k
  have h1 := digit1_nat k
  change decide (k.toNat % 256 ≠ 0) = decide ((wordDigits k 0).val ≠ 0 ∨ (wordDigits k 1).val ≠ 0)
  by_cases h : k.toNat % 256 = 0
  · have hq0 : (wordDigits k 0).val = 0 := by omega
    have hq1 : (wordDigits k 1).val = 0 := by omega
    simp [h, hq0, hq1]
  · have hq : (wordDigits k 0).val ≠ 0 ∨ (wordDigits k 1).val ≠ 0 := by
      by_contra hn
      have hzero := not_or.mp hn
      omega
    have hq' : wordDigits k 0 ≠ 0 ∨ wordDigits k 1 ≠ 0 :=
      hq.imp (fun hn heq => hn (congrArg Fin.val heq)) (fun hn heq => hn (congrArg Fin.val heq))
    simp [h, hq']

/-- No new input carry can vanish from the *set of possible carries*
    as we move to a larger key prefix. -/
private theorem flag_high_of_three (k : Word)
    (h3 : exactCarryFlag k 3 = true) (i : Fin 8)
    (hi : 3 ≤ i.val) : exactCarryFlag k i = true := by
  have hnonzero : k.toNat % nibbleBase (3 : Fin 8) ≠ 0 := by
    exact of_decide_eq_true h3
  have hdiv : nibbleBase (3 : Fin 8) ∣ nibbleBase i := by
    unfold nibbleBase
    exact Nat.pow_dvd_pow 16 (by omega)
  apply decide_eq_true
  intro hzero
  have hmod := Nat.mod_mod_of_dvd k.toNat hdiv
  rw [hzero] at hmod
  simp only [Nat.zero_mod] at hmod
  exact hnonzero hmod.symm

private theorem flag_three_of_nonzero01 (k : Word)
    (h : (wordDigits k 0).val ≠ 0 ∨ (wordDigits k 1).val ≠ 0) : exactCarryFlag k 3 = true := by
  have h0 := digit0_nat k
  have h1 := digit1_nat k
  change decide (k.toNat % 4096 ≠ 0) = true
  apply decide_eq_true
  intro hz
  have hz0 : (wordDigits k 0).val = 0 := by omega
  have hz1 : (wordDigits k 1).val = 0 := by omega
  exact h.elim (fun h => h hz0) (fun h => h hz1)

private theorem flag_three_false_of_all_zero (k : Word) (h0 : wordDigits k 0 = 0)
    (h1 : wordDigits k 1 = 0) (h2 : wordDigits k 2 = 0) : exactCarryFlag k 3 = false := by
  have hv0 := digit0_nat k
  have hv1 := digit1_nat k
  have hv2 := digit2_nat k
  have hz : k.toNat % 4096 = 0 := by
    have heq0 := congrArg Fin.val h0
    have heq1 := congrArg Fin.val h1
    have heq2 := congrArg Fin.val h2
    norm_num at heq0 heq1 heq2
    omega
  simp [exactCarryFlag, nibbleBase, hz]

/-! ## 4. Exact sum decomposition and equality at 72. -/

private theorem prefix3_of_key (k : Word) :
    localPotentialCount 0 (wordDigits k 0) (exactCarryFlag k 0) +
        localPotentialCount 1 (wordDigits k 1) (exactCarryFlag k 1) +
        localPotentialCount 2 (wordDigits k 2) (exactCarryFlag k 2) =
      prefix3 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2) := by
  rw [flag0, flag1, flag2]
  unfold prefix3
  by_cases h0 : (wordDigits k 0).val = 0
  · by_cases h1 : (wordDigits k 1).val = 0
    · simp [h0, h1, score0_correct, score1No_correct, score2No_correct]
    · simp [h0, h1, score0_correct, score1No_correct, score2Yes_correct]
  · simp [h0, score0_correct, score1Yes_correct, score2Yes_correct]

private theorem exactLocalSupportCount_split (k : Word) :
    exactLocalSupportCount k =
      prefix3 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2) +
        localPotentialCount 3 (wordDigits k 3) (exactCarryFlag k 3) +
        localPotentialCount 4 (wordDigits k 4) (exactCarryFlag k 4) +
        localPotentialCount 5 (wordDigits k 5) (exactCarryFlag k 5) +
        localPotentialCount 6 (wordDigits k 6) (exactCarryFlag k 6) +
        localPotentialCount 7 (wordDigits k 7) (exactCarryFlag k 7) := by
  unfold exactLocalSupportCount
  rw [Fin.sum_univ_eight]
  rw [prefix3_of_key]

private theorem prefix3_le26 (q0 q1 q2 : Q) : prefix3 q0 q1 q2 ≤ 26 := by
  revert q0 q1 q2
  decide +kernel

private theorem exact72_implies_components (k : Word) (h : exactLocalSupportCount k = 72) :
    prefix3 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2) = 26 ∧
      exactCarryFlag k 3 = true ∧
      wordDigits k 3 ∈ q3Choices ∧
      exactCarryFlag k 4 = true ∧
      wordDigits k 4 ∈ q4Choices ∧
      exactCarryFlag k 5 = true ∧
      wordDigits k 5 ∈ q5Choices ∧
      exactCarryFlag k 6 = true ∧
      wordDigits k 6 ∈ q6Choices ∧ exactCarryFlag k 7 = true ∧ wordDigits k 7 ∈ q7Choices := by
  rw [exactLocalSupportCount_split] at h
  have hprefix := prefix3_le26 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2)
  have h3 := high_le 3 (wordDigits k 3) (exactCarryFlag k 3) (by omega)
  have h4 := high_le 4 (wordDigits k 4) (exactCarryFlag k 4) (by omega)
  have h5 := high_le 5 (wordDigits k 5) (exactCarryFlag k 5) (by omega)
  have h6 := high_le 6 (wordDigits k 6) (exactCarryFlag k 6) (by omega)
  have h7 := high_le 7 (wordDigits k 7) (exactCarryFlag k 7) (by omega)
  norm_num [highCap] at h3 h4 h5 h6 h7
  have h3eq : localPotentialCount 3 (wordDigits k 3) (exactCarryFlag k 3) = 9 := by omega
  have h4eq : localPotentialCount 4 (wordDigits k 4) (exactCarryFlag k 4) = 10 := by omega
  have h5eq : localPotentialCount 5 (wordDigits k 5) (exactCarryFlag k 5) = 11 := by omega
  have h6eq : localPotentialCount 6 (wordDigits k 6) (exactCarryFlag k 6) = 7 := by omega
  have h7eq : localPotentialCount 7 (wordDigits k 7) (exactCarryFlag k 7) = 9 := by omega
  have hfirst : prefix3 (wordDigits k 0) (wordDigits k 1) (wordDigits k 2) = 26 := by omega
  rcases (high3_eq_iff _ _).mp h3eq with ⟨hc3, hq3⟩
  rcases (high4_eq_iff _ _).mp h4eq with ⟨hc4, hq4⟩
  rcases (high5_eq_iff _ _).mp h5eq with ⟨hc5, hq5⟩
  rcases (high6_eq_iff _ _).mp h6eq with ⟨hc6, hq6⟩
  rcases (high7_eq_iff _ _).mp h7eq with ⟨hc7, hq7⟩
  exact ⟨hfirst, hc3, hq3, hc4, hq4, hc5, hq5, hc6, hq6, hc7, hq7⟩

/-- The complete real-DDT key characterization. No probabilistic
    assumptions and no 32-bit enumeration. -/
theorem support_eq_72_iff_key_class (k : Word) :
    (fastPositiveCells k).card = 72 ↔ isMax72Key k := by
  rw [fixedKey_realSupport_eq_exactLocal]
  constructor
  · intro h
    obtain ⟨hp,hflag3,hq3,_,hq4,_,hq5,_,hq6,_,hq7⟩ :=
      exact72_implies_components k h
    obtain ⟨hq2, hfirst⟩ :=
      (prefix3_eq_26_iff _ _ _).mp hp
    rcases hfirst with ⟨hq0, hq1⟩ | ⟨hq0, hq1⟩
    · rcases hq1 with hzero | hgood
      · have hbad := flag_three_false_of_all_zero k hq0 hzero hq2
        rw [hbad] at hflag3
        contradiction
      · exact ⟨⟨hq2, Or.inl ⟨hq0,hgood⟩⟩,
          hq3,hq4,hq5,hq6,hq7⟩
    · exact ⟨⟨hq2, Or.inr ⟨hq0,hq1⟩⟩,
        hq3,hq4,hq5,hq6,hq7⟩
  · rintro ⟨hp,hq3,hq4,hq5,hq6,hq7⟩
    have hfirst : prefix3 (wordDigits k 0)
      (wordDigits k 1) (wordDigits k 2) = 26 := by
      apply (prefix3_eq_26_iff _ _ _).mpr
      rcases hp with ⟨hq2, hfirst⟩
      exact ⟨hq2, hfirst.elim
        (fun h => Or.inl ⟨h.1, Or.inr h.2⟩)
        (fun h => Or.inr h)⟩
    have hnonzero : (wordDigits k 0).val ≠ 0 ∨
        (wordDigits k 1).val ≠ 0 := by
      rcases hp.2 with ⟨h0,h1⟩ | ⟨h2,h1⟩
      · right
        intro hn
        have hz : wordDigits k 1 = 0 := Fin.ext hn
        rw [hz] at h1
        have hbad : (0 : Q) ∉ q1WhenQ0Zero := by decide
        exact hbad h1
      · left
        intro hn
        have hz : wordDigits k 0 = 0 := Fin.ext hn
        rw [hz] at h2
        have hbad : (0 : Q) ≠ 2 := by decide
        exact hbad h2
    have hf3 := flag_three_of_nonzero01 k hnonzero
    have hf4 := flag_high_of_three k hf3 (4 : Fin 8) (by omega)
    have hf5 := flag_high_of_three k hf3 (5 : Fin 8) (by omega)
    have hf6 := flag_high_of_three k hf3 (6 : Fin 8) (by omega)
    have hf7 := flag_high_of_three k hf3 (7 : Fin 8) (by omega)
    rw [exactLocalSupportCount_split, hf3, hf4, hf5, hf6, hf7, hfirst]
    have h3 := (high3_eq_iff _ _).mpr ⟨rfl,hq3⟩
    have h4 := (high4_eq_iff _ _).mpr ⟨rfl,hq4⟩
    have h5 := (high5_eq_iff _ _).mpr ⟨rfl,hq5⟩
    have h6 := (high6_eq_iff _ _).mpr ⟨rfl,hq6⟩
    have h7 := (high7_eq_iff _ _).mpr ⟨rfl,hq7⟩
    rw [h3,h4,h5,h6,h7]

end Magma.OneHotSupport72KeyClasses
