module

public import Magma.Search.FastSearch
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Independently checked UInt8 no-path certificates

Fast UInt8 code proposes transition edges and forward frontiers. The checker
covers every relevant transition of the original `sboxCarryStep` and verifies
that all paths stay inside the proposed frontiers. An empty final frontier
therefore proves that the original round-function DDT entry is zero.

Acceptance is sufficient for impossibility. Rejection does not establish
positive DDT support, and full equivalence of the UInt8 search and Boolean DP
is not assumed. No correctness theorem about `fastSboxCarryStep` is required.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.Certificates Magma.Certificates.Encoding Magma.FastSearch

namespace Magma.UInt8NoPathCertificates

/-! ## Untrusted, fast proposal -/

/-- Only transitions with the requested output nibble are proposed. -/
def proposeTargetCarryEdges (k d b : V 32) : Array (Array UInt8) :=
  let target := b.rotateRight 11
  ((List.finRange 8).map fun i =>
    fastCarryEdgesAt (fastSboxTables.getD i.val #[])
      (wordDigits k i) (wordDigits d i)
      (nibbleValueMask (wordDigits target i)) true).toArray

/-! ## Independent, original-arithmetic verifier -/

/-- An over-approximation of all original transitions whose output
    equals the requested output nibble.  The arrays are *not* trusted. -/
def verifyTargetCarryEdges (k d b : V 32)
    (E : Array (Array UInt8)) : Bool :=
  let target := b.rotateRight 11
  (List.finRange 8).all fun i =>
    (List.finRange 2).all fun c₀ =>
      (List.finRange 2).all fun c₁ =>
        (List.finRange 16).all fun x =>
          let s : CarryState := (c₀, c₁)
          let step := sboxCarryStep i (wordDigits k i) (wordDigits d i) x s
          (decide (step.1 ≠ wordDigits target i)) ||
            checkedCarryEdge E i s step.2

private theorem verifyTargetCarryEdges_sound (k d b : V 32) (E : Array (Array UInt8))
    (he : verifyTargetCarryEdges k d b E = true) (i : Fin 8) (s : CarryState) (x : Fin 16)
    (hmatch :
      (sboxCarryStep i (wordDigits k i) (wordDigits d i) x s).1 = wordDigits (b.rotateRight 11) i) :
    checkedCarryEdge E i s (sboxCarryStep i (wordDigits k i) (wordDigits d i) x s).2 = true := by
  unfold verifyTargetCarryEdges at he
  have hi := (List.all_eq_true.mp he) i (by simp)
  have h₀ := (List.all_eq_true.mp hi) s.1 (by simp)
  have h₁ := (List.all_eq_true.mp h₀) s.2 (by simp)
  have hx := (List.all_eq_true.mp h₁) x (by simp)
  dsimp only at hx
  simp only [Bool.or_eq_true_iff, decide_eq_true_eq] at hx
  rcases hx with hbad | hedge
  · exact (hbad hmatch).elim
  · exact hedge

/-- Final check, including a verified invariant for ALL eight nibble steps.
    No Boolean witness can be accepted merely because the fast code says so. -/
def verifyUInt8NoPath (k d b : V 32) : Bool :=
  let E := proposeTargetCarryEdges k d b
  let F := fastCarryForward E
  decide (verifyTargetCarryEdges k d b E = true ∧
    verifyForwardCarryFrontiers E F = true ∧
    F.getD 8 0 = (0 : UInt8))

private theorem empty_carry_mask (s : CarryState) :
    carryStateMemFast (0 : UInt8) (checkedCarryIndex s) = false := by
  rcases s with ⟨s₀, s₁⟩
  fin_cases s₀ <;> fin_cases s₁ <;> decide

/-! ## Soundness against the original carry automaton -/

/-- Every accepted fast proposal proves the original DDT entry is zero. -/
theorem verifyUInt8NoPath_sound (k d b : V 32)
    (hv : verifyUInt8NoPath k d b = true) :
    xorDDT_g k d b = 0 := by
  let E := proposeTargetCarryEdges k d b
  let F := fastCarryForward E
  have hparts :
      verifyTargetCarryEdges k d b E = true ∧
      verifyForwardCarryFrontiers E F = true ∧
      F.getD 8 0 = (0 : UInt8) := by
    simpa only [verifyUInt8NoPath, decide_eq_true_eq, E, F] using hv
  obtain ⟨he, hf, hz⟩ := hparts
  by_contra hn
  have hp : 0 < xorDDT_g k d b := Nat.pos_of_ne_zero hn
  have hpath : carryHasPathBoolean (wordDigits k) (wordDigits d)
      (wordDigits (b.rotateRight 11)) = true :=
    (xorDiffPossibleBoolean_iff k d b).mpr hp
  obtain ⟨w⟩ := verifiedCarryPath_of_carryHasPathBoolean
    k d (b.rotateRight 11) hpath
  have hedges : ∀ i : Fin 8,
      checkedCarryEdge E i (w.states i.castSucc) (w.states i.succ) = true := by
    intro i
    have hedge := verifyTargetCarryEdges_sound k d b E he i
      (w.states i.castSucc) (w.input i) (congrArg Prod.fst (w.step i))
    simpa only [w.step i] using hedge
  have hfront := verifyForwardCarryFrontiers_sound
    E F hf w.states w.initial hedges
  have hlast := hfront (⟨8, by decide⟩ : Fin 9)
  rw [hz, empty_carry_mask] at hlast
  cases hlast

/-- For zero-left output difference, one zero second-round g-DDT entry
    eliminates ALL 2^32 choices of the left input difference. -/
theorem threeRound_zeroLeft_of_verifiedUInt8
    (k₀ k₁ k₂ aR bR : V 32)
    (hv : verifyUInt8NoPath k₁ bR aR = true)
    (aL : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) = 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization]
  rw [verifyUInt8NoPath_sound k₁ bR aR hv]
  simp

/-- One-bit columns accepted by the independent no-path checker.
    Each case checks at most `8 * 4 * 16` original transitions, followed
    by verification of the forward-frontier invariant. -/
def certifiedExcludedOneBitBR (k aR : V 32) : List (Fin 32) :=
  (List.finRange 32).filter fun i =>
    verifyUInt8NoPath k (BitVec.ofNat 32 (2 ^ i.val)) aR

theorem certifiedExcludedOneBitBR_sound (k₀ k₁ k₂ aL aR : V 32) (i : Fin 32)
    (hi : i ∈ certifiedExcludedOneBitBR k₁ aR) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂) (aL, aR) (0#32, BitVec.ofNat 32 (2 ^ i.val)) = 0 := by
  exact
    threeRound_zeroLeft_of_verifiedUInt8 k₀ k₁ k₂ aR (BitVec.ofNat 32 (2 ^ i.val))
      (List.mem_filter.mp hi).2 aL

end Magma.UInt8NoPathCertificates
