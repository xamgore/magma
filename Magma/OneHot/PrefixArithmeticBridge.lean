module

public import Magma.OneHot.TraceSplit5
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Arithmetic prefix carries and exact DDT support at bits 20 through 23

The original five-digit trace produces exactly the carry of ordinary
addition of the lower 20 input and key bits. Its attainable carry values
therefore coincide with `WordPrefixCarryPossible` for every 32-bit key.

Combining this bridge with the active-step and silent-suffix reductions
gives exact positive support of the original `g[k]` DDT for input bits
20 through 23 and output difference one. The result follows from the local
key-class table without a Boolean certificate hypothesis, and replacing a
key by its representative preserves support on these four positions.

Excluding one-bit positions outside 20 through 23 is a separate obligation.
-/

open Magma.CarryAutomaton Magma.OneHotTraceSplit5 Magma.OneHotKeyClasses
open Magma.OneHotCarryPrefix Magma.OneHotBoundaryReduction
open Magma.OneHotSilentNibbleStructure Magma.OneHotClassCertificates

namespace Magma.OneHotPrefixArithmeticBridge

/-! ## 1. The exact carry produced by the five silent nibble steps -/

/-- Publicly reproducible description of the step used by the earlier
    `tracePrefix5`. The earlier helper was `private`, so we restate its
    *definition*, not any mathematical assumption. -/
private def prefixStep (key diff target input : Fin 8 → Fin 16)
    (acc : CarryState × Bool) (i : Fin 8) : CarryState × Bool :=
  let step := sboxCarryStep i (key i) (diff i) (input i) acc.1
  (step.2, acc.2 && decide (step.1 = target i))

private theorem tracePrefix5_as_fold (key diff target input : Fin 8 → Fin 16) :
    tracePrefix5 key diff target input =
      Fin.foldl 5
        (fun acc (i : Fin 5) => prefixStep key diff target input acc (i.castLE (by decide)))
        (((0, 0) : CarryState), true) := by
  rfl

/-- Ordinary carry recurrence, written without any S-box operations. -/
def lowCarry5 (key input : Fin 8 → Fin 16) : Fin 2 :=
  nextCarry (input 4) (key 4)
    (nextCarry (input 3) (key 3)
      (nextCarry (input 2) (key 2)
        (nextCarry (input 1) (key 1)
          (nextCarry (input 0) (key 0) 0))))

/-- The silent prefix changes neither the acceptance bit nor the equality
    of the two addition carries. Its actual carry is `lowCarry5`. -/
theorem tracePrefix5_eq_lowCarry5
    (key input : Fin 8 → Fin 16) (r : Fin 4) :
    tracePrefix5 key (oneHotDiffDigits r) oneHotTargetDigits input =
      ((lowCarry5 key input, lowCarry5 key input), true) := by
  simp [tracePrefix5_as_fold, prefixStep, Fin.foldl_succ,
    oneHotDiffDigits, oneHotTargetDigits,
    silent_sbox_step_diagonal, lowCarry5]

/-- The explicit five-step recurrence is the carry of the original
    base-16 addition stream at position five. -/
theorem lowCarry5_word_eq_incomingCarry (k x : V 32) :
    lowCarry5 (wordDigits k) (wordDigits x) =
      incomingCarry (wordDigitStream x) (wordDigitStream k) 5 := by
  simp only [lowCarry5, incomingCarry, ← wordDigitStream_at]
  rfl

/-- The fifth incoming carry equals the ordinary carry from adding the
    lower 20 bits.  Crucially this uses the *previously proved* positional
    carry invariant, not a table of sample keys. -/
theorem incomingCarry5_eq_low20_div (k x : V 32) :
    (incomingCarry (wordDigitStream x) (wordDigitStream k) 5).val =
      ((x.toNat % (2 ^ 20)) + (k.toNat % (2 ^ 20))) / (2 ^ 20) := by
  have hsum := digitPrefixValue_add_carry
    (wordDigitStream x) (wordDigitStream k) 5
  have hout := digitPrefixValue_lt
    (addedDigits (wordDigitStream x) (wordDigitStream k)) 5
  simp only [digitPrefixValue_wordDigitStream] at hsum
  have hp : (16 : Nat) ^ 5 = 2 ^ 20 := by norm_num
  rw [hp] at hsum hout
  have hc := (incomingCarry
    (wordDigitStream x) (wordDigitStream k) 5).isLt
  omega

/-- In the actual trace, the incoming carry at pi_5 depends only on
    the low twenty input and key bits. -/
theorem tracePrefix5_word_carry_eq
    (k x : V 32) (r : Fin 4) :
    (tracePrefix5 (wordDigits k) (oneHotDiffDigits r)
      oneHotTargetDigits (wordDigits x)).1.1.val =
      ((x.toNat % (2 ^ 20)) + (k.toNat % (2 ^ 20))) / (2 ^ 20) := by
  rw [tracePrefix5_eq_lowCarry5, lowCarry5_word_eq_incomingCarry]
  exact incomingCarry5_eq_low20_div k x

/-! ## 2. Exact equivalence of prefix witnesses -/

/-- A five-nibble prefix realizes carry `c` precisely when the ordinary
    low-twenty-bit addition realizes the same carry. -/
theorem wordPrefixCarryPossible_iff_tracePrefix5
    (k : V 32) (c : Fin 2) (r : Fin 4) :
    WordPrefixCarryPossible k c ↔
      ∃ input : Fin 8 → Fin 16,
        tracePrefix5 (wordDigits k) (oneHotDiffDigits r)
          oneHotTargetDigits input = ((c, c), true) := by
  constructor
  · rintro ⟨xLow, hxLow, hdiv⟩
    change xLow < 2 ^ 20 at hxLow
    change (xLow + k.toNat % (2 ^ 20)) / (2 ^ 20) = c.val at hdiv
    let x : V 32 := BitVec.ofNat 32 xLow
    have hxNat : x.toNat = xLow := by
      change (BitVec.ofNat 32 xLow).toNat = xLow
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨wordDigits x, ?_⟩
    rw [tracePrefix5_eq_lowCarry5]
    have hcarry : lowCarry5 (wordDigits k) (wordDigits x) = c := by
      apply Fin.ext
      rw [lowCarry5_word_eq_incomingCarry,
        incomingCarry5_eq_low20_div, hxNat,
        Nat.mod_eq_of_lt hxLow]
      exact hdiv
    simp only [hcarry]
  · rintro ⟨input, hprefix⟩
    let x : V 32 := wordDigitsEquiv.symm input
    have hxDigits : wordDigits x = input :=
      wordDigitsEquiv.apply_symm_apply input
    have hcarry : lowCarry5 (wordDigits k) input = c := by
      have h := congrArg
        (fun s : CarryState × Bool => s.1.1) hprefix
      simpa only [tracePrefix5_eq_lowCarry5] using h
    refine ⟨x.toNat % (2 ^ 20), Nat.mod_lt _ (by norm_num), ?_⟩
    change (x.toNat % (2 ^ 20) + k.toNat % (2 ^ 20)) /
        (2 ^ 20) = c.val
    calc
      _ = (lowCarry5 (wordDigits k) (wordDigits x)).val := by
        rw [lowCarry5_word_eq_incomingCarry,
          incomingCarry5_eq_low20_div]
      _ = c.val := by rw [hxDigits, hcarry]

/-! ## 3. From the full DDT to the already certified local boundary -/

/-- The key nibble computed in the class classifier is exactly the
    digit seen by the original automaton at position five. -/
theorem keyNibble5_eq_wordDigits (k : V 32) :
    keyNibble5 k = wordDigits k 5 := by
  apply Fin.ext
  rw [wordDigits_val]
  change (k.toNat / 2 ^ 20) % 16 =
    k.toNat / 16 ^ 5 % 16
  norm_num

private theorem local_step_equal_carries_iff (q : Fin 16) (c : Fin 2) (r : Fin 4) :
    (∃ x : Fin 16,
        (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)).1 = 2 ∧
          (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)).2.1 =
            (sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)).2.2) ↔
      localOneHotStepPossible q c r = true := by
  rw [localOneHotStepPossible_iff_original_step]
  constructor
  · rintro ⟨x, hout, heq⟩
    let s := sboxCarryStep 5 q (Fin.ofNat 16 (2 ^ r.val)) x (c, c)
    refine ⟨x, s.2.1, ?_⟩
    apply Prod.ext
    · exact hout
    · apply Prod.ext
      · rfl
      · exact heq.symm
  · rintro ⟨x, t, hstep⟩
    refine ⟨x, ?_, ?_⟩
    · exact congrArg Prod.fst hstep
    · rw [hstep]

/-- Replacing just input digit 5 does not change any of the five earlier
    carry transitions. The later digits are irrelevant to this prefix. -/
private theorem tracePrefix5_replace_active
    (key input : Fin 8 → Fin 16) (r : Fin 4) (v : Fin 16) :
    tracePrefix5 key (oneHotDiffDigits r) oneHotTargetDigits
        (fun i => if i = (5 : Fin 8) then v else input i) =
      tracePrefix5 key (oneHotDiffDigits r) oneHotTargetDigits input := by
  rfl

/-- GLOBAL bridge for bits 20..23: positive genuine full-word Magma DDT
    is equivalent to exactly the mathematically proved local condition.
    There is no Boolean verifier premise here. -/
theorem oneHot_middle_pos_iff_keyBoundary (k : V 32) (r : Fin 4) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) ↔
      keyBoundaryPossible k r := by
  rw [oneHot_g_pos_iff_prefix_active]
  unfold keyBoundaryPossible
  rw [← keyNibble5_eq_wordDigits k]
  constructor
  · rintro ⟨input, c, hprefix, hout, heq⟩
    refine ⟨c, ?_, ?_⟩
    · exact (wordPrefixCarryPossible_iff_tracePrefix5 k c r).mpr
        ⟨input, hprefix⟩
    · exact (local_step_equal_carries_iff (keyNibble5 k) c r).mp
        ⟨input 5, hout, heq⟩
  · rintro ⟨c, hcarry, hlocal⟩
    obtain ⟨input, hprefix⟩ :=
      (wordPrefixCarryPossible_iff_tracePrefix5 k c r).mp hcarry
    obtain ⟨v, hout, heq⟩ :=
      (local_step_equal_carries_iff (keyNibble5 k) c r).mpr hlocal
    let input' : Fin 8 → Fin 16 :=
      fun i => if i = (5 : Fin 8) then v else input i
    have hprefix' : tracePrefix5 (wordDigits k)
        (oneHotDiffDigits r) oneHotTargetDigits input' =
        ((c, c), true) := by
      calc
        _ = tracePrefix5 (wordDigits k) (oneHotDiffDigits r)
            oneHotTargetDigits input :=
          tracePrefix5_replace_active (wordDigits k) input r v
        _ = ((c, c), true) := hprefix
    refine ⟨input', c, hprefix', ?_, ?_⟩
    · simpa only [show input' 5 = v from by simp [input']] using hout
    · simpa only [show input' 5 = v from by simp [input']] using heq

/-- Exactly one of the 32 local key classes applies to EACH full key,
    and its four table entries are the genuine DDT support at 20..23. -/
theorem oneHot_middle_pos_iff_localTable (k : V 32) (r : Fin 4) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) ↔
      r ∈ localOneHotSupportedBits
        (keyNibble5 k) (canCarryIntoNibble5 k) := by
  exact (oneHot_middle_pos_iff_keyBoundary k r).trans
    (keyBoundaryPossible_iff_localTable k r)

/-- This proves the key-class invariant on ALL four potentially active
    bit positions, for any two keys in the same class. -/
theorem oneHot_middle_same_class (k k' : V 32)
    (hq : keyNibble5 k = keyNibble5 k')
    (hc : canCarryIntoNibble5 k = canCarryIntoNibble5 k')
    (r : Fin 4) :
    (0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32)) ↔
      (0 < xorDDT_g k' (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32)) := by
  rw [oneHot_middle_pos_iff_localTable,
    oneHot_middle_pos_iff_localTable, hq, hc]

/-- The unconditional representative theorem, on bit positions 20..23. -/
theorem oneHot_middle_representative (k : V 32) (r : Fin 4) :
    (0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32)) ↔
      (0 < xorDDT_g
        (representativeKey (keyNibble5 k) (canCarryIntoNibble5 k))
        (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32)) := by
  apply oneHot_middle_same_class
  · exact (representativeKey_has_class
      (keyNibble5 k) (canCarryIntoNibble5 k)).1.symm
  · exact (representativeKey_has_class
      (keyNibble5 k) (canCarryIntoNibble5 k)).2.symm

/-- Example of a theorem about an entire infinite-looking key class,
    not just the representative 0x00800000. -/
theorem nibble8_no_lower_carry_middle_zero
    (k : V 32)
    (hq : keyNibble5 k = (8 : Fin 16))
    (hc : canCarryIntoNibble5 k = false)
    (r : Fin 4) :
    xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) = 0 := by
  have hnot : ¬ keyBoundaryPossible k r :=
    nibble8_no_lower_carry_boundary_empty k hq hc r
  have hnotpos : ¬ 0 < xorDDT_g k
      (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) := by
    exact fun hp => hnot ((oneHot_middle_pos_iff_keyBoundary k r).mp hp)
  omega

end Magma.OneHotPrefixArithmeticBridge
