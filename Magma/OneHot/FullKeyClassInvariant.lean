module

public import Magma.OneHot.PrefixArithmeticBridge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Full one-bit key-class invariance

A one-bit input difference below bit 20 produces a nonzero output at its
first active nibble, where the required output is zero. Above bit 23,
nibble five is silent and produces zero where the required output is two.
Thus the DDT vanishes outside bits 20 through 23 for every key.

Combining these exclusions with the arithmetic prefix bridge gives an
unconditional local-table classification of all 32 one-bit positions and
proves `OneHotClassInvariant` for every 32-bit round key. The proof uses
structural carry arguments and finite digit arithmetic.
-/

namespace Magma.OneHotFullKeyClassInvariant

open Magma.CarryAutomaton
open Magma.OneHotTraceSplit5
open Magma.OneHotPrefixArithmeticBridge
open Magma.OneHotSilentNibbleStructure
open Magma.OneHotClassCertificates
open Magma.OneHotKeyClasses Magma.OneHotCompleteSupport

/-! ## 1. An eight-step trace as a fixed-length list fold -/

private def traceStep (key diff target input : Fin 8 → Fin 16) (acc : CarryState × Bool)
    (i : Fin 8) : CarryState × Bool :=
  let step := sboxCarryStep i (key i) (diff i) (input i) acc.1
  (step.2, acc.2 && decide (step.1 = target i))

private def allIndices : List (Fin 8) :=
  [0, 1, 2, 3, 4, 5, 6, 7]

private theorem carryTrace_as_list (key diff target input : Fin 8 → Fin 16) :
    carryTrace key diff target input =
      allIndices.foldl (traceStep key diff target input) (((0, 0) : CarryState), true) := by
  rfl

/-- A false acceptance flag cannot be revived by any later nibble. -/
private theorem fold_after_rejection
    (key diff target input : Fin 8 → Fin 16)
    (suffix : List (Fin 8)) (s : CarryState) :
    (suffix.foldl (traceStep key diff target input) (s, false)).2 = false := by
  induction suffix generalizing s with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.foldl_cons]
      have hf :
          (traceStep key diff target input (s, false) i).2 = false := by
        simp [traceStep]
      rcases heq : traceStep key diff target input (s, false) i with ⟨s', flag⟩
      have hflag : flag = false := by simpa [heq] using hf
      subst flag
      exact ih s'

/-- Every zero-difference, zero-target nibble preserves equal carries
    and an already successful acceptance flag. -/
private theorem traceStep_silent
    (key diff target input : Fin 8 → Fin 16)
    (i : Fin 8) (c : Fin 2)
    (hd : diff i = 0) (ht : target i = 0) :
    traceStep key diff target input ((c, c), true) i =
      ((nextCarry (input i) (key i) c,
        nextCarry (input i) (key i) c), true) := by
  simp [traceStep, hd, ht, silent_sbox_step_diagonal]

private theorem fold_silent_prefix (key diff target input : Fin 8 → Fin 16)
    (prefixSteps : List (Fin 8)) :
    (∀ i ∈ prefixSteps, diff i = 0 ∧ target i = 0) →
      ∀ c : Fin 2,
        ∃ c' : Fin 2,
          prefixSteps.foldl (traceStep key diff target input) ((c, c), true) =
            ((c', c'), true) := by
  induction prefixSteps with
  | nil =>
    intro _ c
    exact ⟨c, rfl⟩
  | cons i rest ih =>
    intro hp c
    have hi : diff i = 0 ∧ target i = 0 := hp i (by simp)
    have hrest : ∀ t ∈ rest, diff t = 0 ∧ target t = 0 := by
      intro t ht
      exact hp t (by simp [ht])
    obtain ⟨c', hc'⟩ := ih hrest (nextCarry (input i) (key i) c)
    refine ⟨c', ?_⟩
    simp only [List.foldl_cons]
    rw [traceStep_silent key diff target input i c hi.1 hi.2]
    exact hc'

/-- General first-mismatch lemma: silent synchronized prefix,
    one rejecting step, then an arbitrary suffix. -/
private theorem first_rejection_blocks_trace
    (key diff target input : Fin 8 → Fin 16)
    (prefixSteps suffix : List (Fin 8)) (i : Fin 8)
    (hp : ∀ t ∈ prefixSteps, diff t = 0 ∧ target t = 0)
    (hreject : ∀ c : Fin 2,
      (traceStep key diff target input ((c, c), true) i).2 = false) :
    ((prefixSteps ++ [i] ++ suffix).foldl (traceStep key diff target input)
      (((0, 0) : CarryState), true)).2 = false := by
  obtain ⟨c, hc⟩ := fold_silent_prefix key diff target input prefixSteps hp 0
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hc]
  have hf := hreject c
  rcases hs : traceStep key diff target input ((c, c), true) i with ⟨s, b⟩
  have hb : b = false := by simpa [hs] using hf
  subst b
  exact fold_after_rejection key diff target input suffix s

/-! ## 2. The first conflicting nibble for an arbitrary one-hot bit -/

/-- For j < 20 the first conflict is the input's active nibble;
    for j >= 24 it is nibble 5, which demands output difference 2. -/
private def conflictIndex (j : Fin 32) : Fin 8 :=
  if hj : j.val < 20 then ⟨j.val / 4, by omega⟩ else 5

private def beforeIndex (i : Fin 8) : List (Fin 8) :=
  (List.range i.val).map (fun n => Fin.ofNat 8 n)

private def afterIndex (i : Fin 8) : List (Fin 8) :=
  (List.range (7 - i.val)).map (fun n => Fin.ofNat 8 (i.val + 1 + n))

private theorem allIndices_split (i : Fin 8) :
    allIndices = beforeIndex i ++ [i] ++ afterIndex i := by fin_cases i <;> decide

/-- Pure bit-position bookkeeping on 32 possible positions and 8 digits.
    Only CLOSED constant bit-vector arithmetic is decided here. -/
private theorem silent_before_conflict :
    ∀ j : Fin 32, (j.val < 20 ∨ 24 ≤ j.val) →
      ∀ t : Fin 8, t ∈ beforeIndex (conflictIndex j) →
        wordDigits (oneHot j) t = 0 ∧ oneHotTargetDigits t = 0 := by
  decide

/-- Below bit 20, the conflicting input digit is nonzero and its
    required output digit is zero. Above bit 23, the conflicting input
    digit is zero and its required output digit is two. -/
private theorem conflict_digit_facts :
    ∀ j : Fin 32,
      (j.val < 20 →
        wordDigits (oneHot j) (conflictIndex j) ≠ 0 ∧
        oneHotTargetDigits (conflictIndex j) = 0) ∧
      (24 ≤ j.val →
        wordDigits (oneHot j) (conflictIndex j) = 0 ∧
        oneHotTargetDigits (conflictIndex j) = 2) := by
  decide

/-- The conflicting step rejects regardless of the key, input digit,
    and synchronized carry bit. -/
private theorem traceStep_rejects_conflict
    (key input : Fin 8 → Fin 16) (j : Fin 32)
    (hj : j.val < 20 ∨ 24 ≤ j.val) (c : Fin 2) :
    (traceStep key (wordDigits (oneHot j))
      oneHotTargetDigits input ((c, c), true) (conflictIndex j)).2 = false := by
  by_cases hl : j.val < 20
  · obtain ⟨hd, ht⟩ := (conflict_digit_facts j).1 hl
    have hn := active_sbox_step_nonzero
      (conflictIndex j) (key (conflictIndex j))
      (wordDigits (oneHot j) (conflictIndex j))
      (input (conflictIndex j)) c hd
    simp [traceStep, ht, hn]
  · have hh : 24 ≤ j.val := by omega
    obtain ⟨hd, ht⟩ := (conflict_digit_facts j).2 hh
    have hs := silent_sbox_step_diagonal
      (conflictIndex j) (key (conflictIndex j))
      (input (conflictIndex j)) c
    simp [traceStep, hd, ht, hs]

/-- No 8-nibble input assignment can be accepted when the active
    bit lies outside positions 20..23. -/
theorem oneHot_trace_outside_false
    (key input : Fin 8 → Fin 16) (j : Fin 32)
    (hj : j.val < 20 ∨ 24 ≤ j.val) :
    (carryTrace key (wordDigits (oneHot j))
      oneHotTargetDigits input).2 = false := by
  rw [carryTrace_as_list, allIndices_split (conflictIndex j)]
  exact first_rejection_blocks_trace
    key (wordDigits (oneHot j)) oneHotTargetDigits input
    (beforeIndex (conflictIndex j)) (afterIndex (conflictIndex j))
    (conflictIndex j)
    (silent_before_conflict j hj)
    (traceStep_rejects_conflict key input j hj)

/-- Structural key-independent impossibility of the other 28 one-bit
    input differences. This theorem concerns the genuine full-word DDT. -/
theorem oneHot_outside_middle_zero
    (k : V 32) (j : Fin 32)
    (hj : j.val < 20 ∨ 24 ≤ j.val) :
    xorDDT_g k (oneHot j) (1#32) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  have hrotation : rot11 (0x00200000#32) = (1#32) := by decide
  rw [← hrotation] at hp
  obtain ⟨input, haccept⟩ :=
    (xorDDT_g_pos_iff_exists_trace k (oneHot j)
      (0x00200000#32)).mp hp
  rw [wordDigits_oneHot_output] at haccept
  have hfalse := oneHot_trace_outside_false (wordDigits k) input j hj
  rw [hfalse] at haccept
  exact Bool.noConfusion haccept

/-! ## 3. Unconditional exact support theorem (no certificates) -/

/-- COMPLETE analytic classification for arbitrary key and arbitrary
    one-bit input difference. The local table has only four indices;
    the other 28 input positions have identically zero DDT.

    Unlike the earlier checkedPredictedOneHotSupport_iff, this has NO
    Boolean-verifier hypothesis and applies to every key at once. -/
theorem oneHot_all_pos_iff_localTable
    (k : V 32) (j : Fin 32) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
      ∃ r : Fin 4,
        j.val = 20 + r.val ∧
          r ∈ localOneHotSupportedBits
            (keyNibble5 k) (canCarryIntoNibble5 k) := by
  constructor
  · intro hp
    have hmiddle : 20 ≤ j.val ∧ j.val < 24 := by
      by_contra hn
      have hout : j.val < 20 ∨ 24 ≤ j.val := by omega
      have hz := oneHot_outside_middle_zero k j hout
      change 0 < xorDDT_g k (oneHot j) (1#32) at hp
      omega
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j.val = 20 + r.val := by
      dsimp [r]
      omega
    refine ⟨r, hr, ?_⟩
    apply (oneHot_middle_pos_iff_localTable k r).mp
    simpa only [hr] using hp
  · rintro ⟨r, hr, hlocal⟩
    have hp := (oneHot_middle_pos_iff_localTable k r).mpr hlocal
    simpa only [hr] using hp

/-! ## 4. Close the universal key-class invariant -/

/-- Every bit position outside the active nibble has DDT count zero,
    while all four positions in the active nibble preserve support on
    replacing the key by its 32-class representative. -/
theorem oneHot_full_representative (k : V 32) (j : Fin 32) :
    (0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32)) ↔
    (0 < xorDDT_g
      (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k))
      (BitVec.ofNat 32 (2 ^ j.val)) (1#32)) := by
  by_cases hout : j.val < 20 ∨ 24 ≤ j.val
  · have hz := oneHot_outside_middle_zero k j hout
    have hzRep := oneHot_outside_middle_zero
      (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k)) j hout
    simp only [oneHot] at hz hzRep
    simp [hz, hzRep]
  · have hmiddle : 20 ≤ j.val ∧ j.val < 24 := by omega
    let r : Fin 4 := ⟨j.val - 20, by omega⟩
    have hr : j.val = 20 + r.val := by
      dsimp [r]
      omega
    rw [hr]
    exact oneHot_middle_representative k r

/-- The outstanding proposition from OneHotClassCertificates is
    now proved WITHOUT any Boolean verifier premise. -/
theorem oneHotClassInvariant : OneHotClassInvariant := by
  intro k j
  exact oneHot_full_representative k j

/-- If the independent 32-representative certificate has been checked,
    this recovers the full support theorem for every 32-bit key.
    The structural invariance proof itself is unconditional. -/
theorem allKeys_oneHot_support_of_representative_certificate
    (hcert : verifyAllRepresentativeClasses = true)
    (k : V 32) (j : Fin 32) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ j.val)) (1#32) ↔
      j ∈ predictedOneHotPositions k := by
  exact allKeys_support_of_classInvariant hcert oneHotClassInvariant k j

end Magma.OneHotFullKeyClassInvariant
