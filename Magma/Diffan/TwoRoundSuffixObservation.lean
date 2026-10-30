module

import all Init.Data.Range.Basic
public import Magma.Diffan.ScheduledCorrectionMaskedOutputs
public import Magma.Diffan.AllKeyFeistelCorrection
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Two ordinary scheduled rounds: an exact inverse-coordinate endpoint

We now impose a genuine output predicate after two ordinary G rounds.
Unlike the left output base after one round, the left base after two
rounds depends nonlinearly on the initial right base.  In fact it has no
uniform XOR response to 0x6000, for any master key.

The final pair does retain an exactly recoverable coordinate:
    (G[j] (G[i] (L,R))).right XOR g[j] ((G[j] (G[i] (L,R))).left) = R.
Thus a mask of this *last-round-unwound right base* gives a nontrivial
endpoint condition, compatible with the partner involution R -> R XOR t.

This output observation depends on the last round key, so it is not
claimed to be an ordinary key-independent ciphertext-bit condition.
The correction count is an exact selected midpoint fiber under one
256-bit master.
-/

namespace Magma.DiffanTwoRoundSuffixObservation

open Magma
open Magma.DiffanScheduledMeet
open Magma.DiffanFeistelDeltaPropagation
open Magma.DiffanAllKeyFeistelCorrection
open Magma.DiffanScheduledCorrectionReachability
open Magma.DiffanScheduledCorrectionHomogeneity
open Magma.DiffanScheduledCorrectionPartnerFibers
open Magma.DiffanScheduledCorrectionMaskedInputs
open Magma.DiffanScheduledCorrectionMaskedOutputs

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Diffan.StateDifference (Word × Word) (Word × Word)

/-- The left base after two chronological ordinary G rounds. -/
theorem twoRound_leftBase
    (master : Master) (i j : Fin 32) (p : Point) :
    (rightEquiv [i, j] master p).base.1 =
      xor (g (roundKey master i) p.base.2) p.base.1 := by
  rcases p with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  change (G (roundKey master j)
    (G (roundKey master i) (L, R))).1 = _
  rfl

/-- The right base after two rounds is the original right base XOR
    the last round function evaluated at the new left base. -/
theorem twoRound_rightBase
    (master : Master) (i j : Fin 32) (p : Point) :
    (rightEquiv [i, j] master p).base.2 =
      xor (g (roundKey master j)
        (xor (g (roundKey master i) p.base.2) p.base.1)) p.base.2 := by
  rcases p with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  change (G (roundKey master j)
    (G (roundKey master i) (L, R))).2 = _
  rfl

/-- Undo only the final round's contribution to the final right base.
    This is a genuine observable function of the final state and the
    last scheduled round key. -/
def unwindLastRight (master : Master) (j : Fin 32) (p : Point) : Word :=
  p.base.2 ^^^ g (roundKey master j) p.base.1

/-- The decoded coordinate is exactly the initial right base. -/
theorem twoRound_unwindLastRight
    (master : Master) (i j : Fin 32) (p : Point) :
    unwindLastRight master j (rightEquiv [i, j] master p) = p.base.2 := by
  rw [unwindLastRight, twoRound_rightBase, twoRound_leftBase]
  change
    (g (roundKey master j)
      (xor (g (roundKey master i) p.base.2) p.base.1) ^^^ p.base.2) ^^^
      g (roundKey master j)
        (xor (g (roundKey master i) p.base.2) p.base.1) = p.base.2
  have cancel (x y : Word) : (x ^^^ y) ^^^ x = y := by
    rw [BitVec.xor_comm x y, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  exact cancel _ _

/-- A nontrivial output condition after two actual scheduled rounds. -/
def outputUnwoundRightMask
    (master : Master) (j : Fin 32) (mask target : Word) (p : Point) : Prop :=
  (unwindLastRight master j p &&& mask) = (target &&& mask)

/-- True two-round midpoint admissibility becomes two masks of the same
    initial right base, without dropping any actual trajectory. -/
theorem twoRound_admitted_iff
    (master : Master) (i j : Fin 32)
    (inMask inTarget outMask outTarget L aL d R : Word) :
    admittedAt [] [i, j] master
        (inputRightMask inMask inTarget)
        (outputUnwoundRightMask master j outMask outTarget)
        L aL d R ↔
      (R &&& inMask) = (inTarget &&& inMask) ∧
      (R &&& outMask) = (outTarget &&& outMask) := by
  change
    (inputRightMask inMask inTarget
      ((leftEquiv [] master).symm (middleAt L aL d R)) ∧
     outputUnwoundRightMask master j outMask outTarget
       (rightEquiv [i, j] master (middleAt L aL d R))) ↔ _
  rw [empty_prefix_symm]
  change
    ((R &&& inMask) = (inTarget &&& inMask) ∧
      ((unwindLastRight master j
        (rightEquiv [i, j] master (middleAt L aL d R))) &&& outMask) =
        (outTarget &&& outMask)) ↔ _
  rw [twoRound_unwindLastRight]
  rfl

/-- Agreement on two masks is equivalent to agreement on their bitwise union. -/
private theorem xor_mask_union
    (R d m n : Word) :
    ((R &&& m) = (d &&& m) ∧ (R &&& n) = (d &&& n)) ↔
      (R &&& (m ||| n)) = (d &&& (m ||| n)) := by
  bv_decide

/-- Combining the two real endpoint conditions does not introduce
    additional intermediate-state guesses. -/
theorem twoRound_count_eq_combined_mask
    (master : Master) (i j q : Fin 32)
    (inMask outMask L aL d t b : Word) :
    scheduledCorrectionCount [] [i, j] master q
      (inputRightMask inMask d)
      (outputUnwoundRightMask master j outMask d)
      L aL d t b =
    scheduledCorrectionCount [] [i, j] master q
      (inputRightMask (inMask ||| outMask) d)
      (fun _ => True) L aL d t b := by
  rw [scheduledCorrectionCount_spec, scheduledCorrectionCount_spec]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [twoRound_admitted_iff, masked_admitted_iff]
  constructor
  · rintro ⟨hm, hc⟩
    refine ⟨?_, hc⟩
    exact (xor_mask_union R d inMask outMask).mp hm
  · rintro ⟨hm, hc⟩
    refine ⟨?_, hc⟩
    exact (xor_mask_union R d inMask outMask).mpr hm

/-- Masks hiding the partner direction preserve even correction-fiber
    cardinalities under the two-round endpoint condition. -/
theorem twoRound_all_counts_even
    (master : Master) (i j q : Fin 32)
    (inMask outMask L aL d t b : Word)
    (ht : t ≠ 0#32)
    (hIn : (t &&& inMask) = 0#32)
    (hOut : (t &&& outMask) = 0#32) :
    ∃ n : Nat, scheduledCorrectionCount [] [i, j] master q
      (inputRightMask inMask d)
      (outputUnwoundRightMask master j outMask d)
      L aL d t b = 2 * n := by
  rw [twoRound_count_eq_combined_mask]
  apply masked_slice_even [i, j] master q (inMask ||| outMask) d L aL d t b ht
  bv_decide

/-- A shared left base cancels from the XOR of the two round outputs. -/
private theorem common_left_cancels (x y L : Word) :
    (x ^^^ L) ^^^ (y ^^^ L) = y ^^^ x := by
  calc
    (x ^^^ L) ^^^ (y ^^^ L) = (L ^^^ L) ^^^ (y ^^^ x) := by ac_rfl
    _ = y ^^^ x := by simp

/-- Two concrete initial right bases demonstrate that the left-output
    XOR response is not constant. -/
theorem leftBase_shift6000_two_witnesses
    (master : Master) (i j : Fin 32) (L aL d : Word) :
    ((rightEquiv [i, j] master
        (middleAt L aL d (0#32))).base.1 ^^^
      (rightEquiv [i, j] master
        (middleAt L aL d (0x00006000#32))).base.1) ≠
    ((rightEquiv [i, j] master
        (middleAt L aL d (0x00001000#32))).base.1 ^^^
      (rightEquiv [i, j] master
        (middleAt L aL d (0x00007000#32))).base.1) := by
  simp only [twoRound_leftBase, middleAt]
  change
    (g (roundKey master i) (0#32) ^^^ L) ^^^
      (g (roundKey master i) (0x00006000#32) ^^^ L) ≠
    (g (roundKey master i) (0x00001000#32) ^^^ L) ^^^
      (g (roundKey master i) (0x00007000#32) ^^^ L)
  rw [common_left_cancels, common_left_cancels]
  exact shift6000_two_witnesses (roundKey master i)

/-- In particular there is no key-independent *or even key-specific*
    constant u that describes the two-round left output response for
    all right bases R. -/
theorem leftBase_shift6000_not_uniform
    (master : Master) (i j : Fin 32) (L aL d : Word) :
    ¬ ∃ u : Word, ∀ R : Word,
      (rightEquiv [i, j] master
        (middleAt L aL d R)).base.1 ^^^
      (rightEquiv [i, j] master
        (middleAt L aL d (R ^^^ (0x00006000#32)))).base.1 = u := by
  rintro ⟨u, hu⟩
  have h0 := hu (0#32)
  have h1 := hu (0x00001000#32)
  have h6 : ((0#32) ^^^ (0x00006000#32)) = (0x00006000#32 : Word) := by decide
  have h7 : ((0x00001000#32) ^^^ (0x00006000#32)) = (0x00007000#32 : Word) := by decide
  rw [h6] at h0
  rw [h7] at h1
  exact leftBase_shift6000_two_witnesses master i j L aL d
    (h0.trans h1.symm)

/-- Chosen endpoint masks retain a real 16-element family of right
    middle bases and keep both obstruction witnesses (for any master). -/
theorem chosen_twoRound_two_distinct_positive_fibers
    (master : Master) (i j q : Fin 32) (L aL d : Word) :
    ∃ b₀ b₁ : Word, b₀ ≠ b₁ ∧
      0 < scheduledCorrectionCount [] [i, j] master q
        (inputRightMask upperInputMask d)
        (outputUnwoundRightMask master j lowerOutputMask d)
        L aL d (0x00006000#32) b₀ ∧
      0 < scheduledCorrectionCount [] [i, j] master q
        (inputRightMask upperInputMask d)
        (outputUnwoundRightMask master j lowerOutputMask d)
        L aL d (0x00006000#32) b₁ := by
  have h0 : admittedAt [] [i, j] master
      (inputRightMask upperInputMask d)
      (outputUnwoundRightMask master j lowerOutputMask d)
      L aL d ((0#32) ^^^ d) := by
    apply (twoRound_admitted_iff master i j upperInputMask d
      lowerOutputMask d L aL d ((0#32) ^^^ d)).mpr
    constructor <;> bv_decide
  have h1 : admittedAt [] [i, j] master
      (inputRightMask upperInputMask d)
      (outputUnwoundRightMask master j lowerOutputMask d)
      L aL d ((0x00001000#32) ^^^ d) := by
    apply (twoRound_admitted_iff master i j upperInputMask d
      lowerOutputMask d L aL d ((0x00001000#32) ^^^ d)).mpr
    constructor <;> (simp only [upperInputMask, lowerOutputMask]; bv_decide)
  exact two_positive_distinct_correction_slices [] [i, j] master q
    (inputRightMask upperInputMask d)
    (outputUnwoundRightMask master j lowerOutputMask d)
    L aL d h0 h1

/-- Chosen two-endpoint observations force even fiber sizes. -/
theorem chosen_twoRound_all_counts_even
    (master : Master) (i j q : Fin 32) (L aL d b : Word) :
    ∃ n : Nat, scheduledCorrectionCount [] [i, j] master q
      (inputRightMask upperInputMask d)
      (outputUnwoundRightMask master j lowerOutputMask d)
      L aL d (0x00006000#32) b = 2 * n := by
  exact twoRound_all_counts_even master i j q upperInputMask
    lowerOutputMask L aL d (0x00006000#32) b
    (by decide) (by decide) (by decide)

end Magma.DiffanTwoRoundSuffixObservation
