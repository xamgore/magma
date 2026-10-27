module

public import Magma.OneHotBoundaryReduction
import all Init.Data.Range.Basic

@[expose] public section

/-!
# The original eight-digit carry trace split into five plus one plus two

Positive round-function DDT is equivalent to an accepted assignment of eight
input digits. The original fold is then split exactly after its five-digit
prefix, leaving the active nibble five and the two silent suffix nibbles.
For a fixed assignment, acceptance depends only on the common prefix carry,
the active output digit two, and equal outgoing carries from that active step.
-/

open Magma.CarryAutomaton Magma.OneHotSilentNibbleStructure Magma.OneHotBoundaryReduction

namespace Magma.OneHotTraceSplit5

/-! ## 1. Positivity is existence of an accepted original carry trace -/

/-- Converts a positive full-word DDT into a concrete eight-digit witness.
    This follows from the already proved equality of counting functions;
    it does not evaluate the huge finite set. -/
theorem xorDDT_g_pos_iff_exists_trace (k d out : V 32) :
    0 < xorDDT_g k d (rot11 out) ↔
      ∃ input : Fin 8 → Fin 16,
        (carryTrace (wordDigits k) (wordDigits d)
          (wordDigits out) input).2 = true := by
  rw [xorDDT_g_eq_carryMatrixCount,
      ← carryWordCount_eq_carryMatrixCount,
      carryWordCount_eq_digitAssignments]
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and]

/-! ## 2. The two special digit patterns -/

/-- One active input difference at nibble 5, bit r of that nibble. -/
def oneHotDiffDigits (r : Fin 4) (i : Fin 8) : Fin 16 :=
  if i = 5 then Fin.ofNat 16 (2 ^ r.val) else 0

/-- Before the final rotation, output difference 1 lies at bit 21,
    i.e. output digit 2 of S-box number 5. -/
def oneHotTargetDigits (i : Fin 8) : Fin 16 :=
  if i = 5 then 2 else 0

/-- The precise 32-bit input difference has just one active nibble. -/
theorem wordDigits_oneHot_input (r : Fin 4) :
    wordDigits (BitVec.ofNat 32 (2 ^ (20 + r.val))) =
      oneHotDiffDigits r := by
  funext i
  fin_cases i <;> fin_cases r <;> decide

/-- The inverse-rotated output difference of 1 has nibble 5 equal to 2. -/
theorem wordDigits_oneHot_output :
    wordDigits (0x00200000#32) = oneHotTargetDigits := by
  decide

private theorem rotated_target_one : rot11 (0x00200000#32) = (1#32) := by decide

/-- Full DDT support at bit 20+r, expressed through the ORIGINAL
    deterministic automaton with its one active input/output nibble. -/
theorem oneHot_pos_iff_exists_trace (k : V 32) (r : Fin 4) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) ↔
      ∃ input : Fin 8 → Fin 16,
        (carryTrace (wordDigits k)
          (oneHotDiffDigits r) oneHotTargetDigits input).2 = true := by
  rw [← rotated_target_one]
  rw [xorDDT_g_pos_iff_exists_trace]
  rw [wordDigits_oneHot_input, wordDigits_oneHot_output]

/-! ## 3. Splitting Fin.foldl 8 exactly into 5+1+2 -/

/-- One step, using precisely the same transition and flag as carryTrace. -/
private def traceStep (key diff target input : Fin 8 → Fin 16)
    (acc : CarryState × Bool) (i : Fin 8) : CarryState × Bool :=
  let step := sboxCarryStep i (key i) (diff i) (input i) acc.1
  (step.2, acc.2 && decide (step.1 = target i))

/-- State and acceptance flag after the first five original nibble steps. -/
def tracePrefix5 (key diff target input : Fin 8 → Fin 16) :
    CarryState × Bool :=
  Fin.foldl 5 (fun acc (i : Fin 5) =>
    traceStep key diff target input acc
      (i.castLE (by decide))) (((0, 0) : CarryState), true)

/-- Pure algebra of the fold.  The last three steps are indices 5,6,7.
    No S-box table evaluation is involved in this theorem. -/
theorem carryTrace_split_after_five
    (key diff target input : Fin 8 → Fin 16) :
    carryTrace key diff target input =
      traceStep key diff target input
        (traceStep key diff target input
          (traceStep key diff target input
            (tracePrefix5 key diff target input) 5) 6) 7 := by
  change Fin.foldl (5 + 3) (traceStep key diff target input)
    (((0, 0) : CarryState), true) = _
  rw [Fin.foldl_add]
  rfl

/-! ## 4. The silent prefix and the nonempty silent suffix -/

/-- Starting from equal carries, the first five inactive digits
    reach equal carries and accept every local target-zero test. -/
theorem oneHot_prefix5_diagonal
    (key input : Fin 8 → Fin 16) (r : Fin 4) :
    ∃ c : Fin 2,
      tracePrefix5 key (oneHotDiffDigits r) oneHotTargetDigits input =
        ((c, c), true) := by
  let c₁ := nextCarry (input 0) (key 0) 0
  let c₂ := nextCarry (input 1) (key 1) c₁
  let c₃ := nextCarry (input 2) (key 2) c₂
  let c₄ := nextCarry (input 3) (key 3) c₃
  let c₅ := nextCarry (input 4) (key 4) c₄
  refine ⟨c₅, ?_⟩
  simp [tracePrefix5, traceStep, Fin.foldl_succ,
    oneHotDiffDigits, oneHotTargetDigits,
    silent_sbox_step_diagonal, c₁, c₂, c₃, c₄, c₅]

/-- The suffix steps at indices 6 and 7 are just the earlier `silentRun`
    applied to a concrete two-element list.  Only its Boolean flag
    is relevant: the final outgoing carry is intentionally unrestricted. -/
private theorem two_silent_suffix_iff (key input : Fin 8 → Fin 16)
    (r : Fin 4) (s : CarryState) :
    (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
      (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
        (s, true) 6) 7).2 = true ↔ s.1 = s.2 := by
  have h := nonempty_silent_suffix_iff_diagonal
    (6 : Fin 8) (key 6) (input 6) [(7, key 7, input 7)] s
  simpa [silentRun, traceStep, oneHotDiffDigits,
    oneHotTargetDigits, Bool.and_assoc] using h

/-! ## 5. Fixed-word criterion — active step with equal outgoing carries -/

/-- Exact, unconditional criterion for a fixed assignment of the 8 digits.
    The first five digits contribute ONLY their common carry `c`.
    The last two accept iff the active step has equal outgoing carries. -/
theorem oneHot_trace_iff_active
    (key input : Fin 8 → Fin 16) (r : Fin 4)
    (c : Fin 2)
    (hprefix : tracePrefix5 key (oneHotDiffDigits r)
      oneHotTargetDigits input = ((c, c), true)) :
    (carryTrace key (oneHotDiffDigits r) oneHotTargetDigits input).2 = true ↔
      (sboxCarryStep 5 (key 5) (Fin.ofNat 16 (2 ^ r.val))
        (input 5) (c, c)).1 = 2 ∧
      (sboxCarryStep 5 (key 5) (Fin.ofNat 16 (2 ^ r.val))
        (input 5) (c, c)).2.1 =
      (sboxCarryStep 5 (key 5) (Fin.ofNat 16 (2 ^ r.val))
        (input 5) (c, c)).2.2 := by
  rw [carryTrace_split_after_five, hprefix]
  let active := sboxCarryStep 5 (key 5)
    (Fin.ofNat 16 (2 ^ r.val)) (input 5) (c, c)
  have hsuffix := two_silent_suffix_iff key input r active.2
  change
    (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
      (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
        (active.2, decide (active.1 = 2)) 6) 7).2 = true ↔
       active.1 = 2 ∧ active.2.1 = active.2.2
  have hflag :
      (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
        (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
          (active.2, decide (active.1 = 2)) 6) 7).2 =
        (decide (active.1 = 2) &&
          (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
            (traceStep key (oneHotDiffDigits r) oneHotTargetDigits input
              (active.2, true) 6) 7).2) := by
    simp only [traceStep, Bool.true_and, Bool.and_assoc]
    rfl
  rw [hflag]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr_right (fun _ => hsuffix)

/-! ## 6. Full round-function DDT, with the remaining existential explicit -/

/-- This is now a theorem about the ACTUAL 32-bit `g[k]` DDT, not about
    an auxiliary Boolean table.  Its only witnesses are the eight
    4-bit input digits and their common incoming carry at nibble 5.

    All contributions of the upper two nibbles have disappeared from
    the condition, because their input/output differences are zero. -/
theorem oneHot_g_pos_iff_prefix_active (k : V 32) (r : Fin 4) :
    0 < xorDDT_g k (BitVec.ofNat 32 (2 ^ (20 + r.val))) (1#32) ↔
      ∃ (input : Fin 8 → Fin 16) (c : Fin 2),
        tracePrefix5 (wordDigits k) (oneHotDiffDigits r)
          oneHotTargetDigits input = ((c, c), true) ∧
        (sboxCarryStep 5 ((wordDigits k) 5)
          (Fin.ofNat 16 (2 ^ r.val)) (input 5) (c, c)).1 = 2 ∧
        (sboxCarryStep 5 ((wordDigits k) 5)
          (Fin.ofNat 16 (2 ^ r.val)) (input 5) (c, c)).2.1 =
        (sboxCarryStep 5 ((wordDigits k) 5)
          (Fin.ofNat 16 (2 ^ r.val)) (input 5) (c, c)).2.2 := by
  rw [oneHot_pos_iff_exists_trace]
  constructor
  · rintro ⟨input, htrace⟩
    obtain ⟨c, hprefix⟩ := oneHot_prefix5_diagonal (wordDigits k) input r
    exact ⟨input, c, hprefix,
      (oneHot_trace_iff_active (wordDigits k) input r c hprefix).mp htrace⟩
  · rintro ⟨input, c, hprefix, hout, hcarry⟩
    exact ⟨input,
      (oneHot_trace_iff_active (wordDigits k) input r c hprefix).mpr
        ⟨hout, hcarry⟩⟩

end Magma.OneHotTraceSplit5
