module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledCorrectionMaskedInputs
import Std.Tactic.BVDecide

@[expose] public section

/-!
# A nontrivial masked output endpoint for a genuine one-round suffix

The previous masked-input result allowed an arbitrary suffix, but its output
predicate was True.  Here the suffix contains one actual scheduled ordinary
Magma G round, and we observe some bits of the left output base.

For G[k](L,R) = (R, L XOR g[k](R)), the left output base is precisely R,
independently of the round key.  Thus an output mask invisible to the
right-midpoint translation R -> R XOR t is a genuine, key-independent
endpoint condition preserved by the correction partner involution.

We take two different masks: the input condition fixes the upper 16 bits
of R and the output condition fixes its lower 12 bits.  Their intersection
leaves four free bits (12..15), including the direction 0x6000 and the
0x1000 witness separation.  Both independently constrain the endpoints.

Every restricted correction coefficient is even, and for each master key
there are two distinct positive correction fibers.
-/

namespace Magma.DifanScheduledCorrectionMaskedOutputs

open Magma
open Magma.DifanScheduledMeet
open Magma.DifanScheduledCorrectionReachability
open Magma.DifanScheduledCorrectionHomogeneity
open Magma.DifanScheduledCorrectionMaskedInputs
open Magma.DifanScheduledCorrectionPartnerFibers

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Difan.StateDifference (Word × Word) (Word × Word)

/-- Observe the masked left base of the actual final pair.  Unlike a
    condition on a difference, this is a concrete endpoint-state predicate. -/
def outputLeftBaseMask (mask target : Word) (p : Point) : Prop :=
  (p.base.1 &&& mask) = (target &&& mask)

/-- After one ordinary scheduled G round, the left output base is the
    right input base.  In particular this identity has no key hypothesis. -/
theorem oneRound_leftBase (master : Master) (j : Fin 32) (p : Point) :
    (rightEquiv [j] master p).base.1 = p.base.2 := by
  rcases p with ⟨⟨L, R⟩, ⟨aL, aR⟩⟩
  change (G (roundKey master j) (L, R)).1 = R
  rfl

/-- Exact, not over-approximated, midpoint admissibility with a
    key-independent input mask and a key-independent output mask. -/
theorem oneRound_admitted_iff
    (master : Master) (j : Fin 32)
    (inMask inTarget outMask outTarget L aL d R : Word) :
    admittedAt [] [j] master
        (inputRightMask inMask inTarget)
        (outputLeftBaseMask outMask outTarget) L aL d R ↔
      (R &&& inMask) = (inTarget &&& inMask) ∧
      (R &&& outMask) = (outTarget &&& outMask) := by
  change
    (inputRightMask inMask inTarget
      ((leftEquiv [] master).symm (middleAt L aL d R)) ∧
     outputLeftBaseMask outMask outTarget
      (rightEquiv [j] master (middleAt L aL d R))) ↔ _
  rw [empty_prefix_symm]
  change
    ((R &&& inMask) = (inTarget &&& inMask) ∧
     (((rightEquiv [j] master (middleAt L aL d R)).base.1 &&& outMask) =
        (outTarget &&& outMask))) ↔ _
  rw [oneRound_leftBase]
  rfl

/-- A conjunction of two masked observations with the same target
    is exactly the single observation of their bitwise union. -/
private theorem two_masks_iff (R d maskA maskB : Word) :
    ((R &&& maskA) = (d &&& maskA) ∧
     (R &&& maskB) = (d &&& maskB)) ↔
      (R &&& (maskA ||| maskB)) = (d &&& (maskA ||| maskB)) := by
  bv_decide

/-- The genuine one-round output restriction can be absorbed into a
    combined mask only for this specific Feistel output coordinate.
    This makes the existing parity theorem reusable without copying it. -/
theorem oneRound_count_eq_combined_mask
    (master : Master) (i j : Fin 32)
    (inMask outMask L aL d t b : Word) :
    scheduledCorrectionCount [] [j] master i
      (inputRightMask inMask d) (outputLeftBaseMask outMask d)
      L aL d t b =
    scheduledCorrectionCount [] [j] master i
      (inputRightMask (inMask ||| outMask) d) (fun _ => True)
      L aL d t b := by
  rw [scheduledCorrectionCount_spec, scheduledCorrectionCount_spec]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [oneRound_admitted_iff,
    masked_admitted_iff]
  constructor
  · rintro ⟨hmask, hcorr⟩
    exact ⟨(two_masks_iff R d inMask outMask).mp hmask, hcorr⟩
  · rintro ⟨hmask, hcorr⟩
    exact ⟨(two_masks_iff R d inMask outMask).mpr hmask, hcorr⟩

/-- If neither endpoint mask sees t, the genuine midpoint admissibility
    relation is partner-closed even with a nonempty scheduled suffix. -/
theorem oneRound_partner_admitted
    (master : Master) (j : Fin 32)
    (inMask outMask L aL d t R : Word)
    (hIn : (t &&& inMask) = 0#32)
    (hOut : (t &&& outMask) = 0#32)
    (h : admittedAt [] [j] master
      (inputRightMask inMask d) (outputLeftBaseMask outMask d)
      L aL d R) :
    admittedAt [] [j] master
      (inputRightMask inMask d) (outputLeftBaseMask outMask d)
      L aL d (R ^^^ t) := by
  obtain ⟨ha, hb⟩ := (oneRound_admitted_iff master j
    inMask d outMask d L aL d R).mp h
  apply (oneRound_admitted_iff master j
    inMask d outMask d L aL d (R ^^^ t)).mpr
  exact ⟨(masked_xor_invariant R inMask t hIn).trans ha,
    (masked_xor_invariant R outMask t hOut).trans hb⟩

/-- Every correction slice for both real endpoint conditions is even.
    The proof reuses the already established generic partner-orbit count. -/
theorem oneRound_all_counts_even
    (master : Master) (i j : Fin 32)
    (inMask outMask L aL d t b : Word)
    (ht : t ≠ 0#32)
    (hIn : (t &&& inMask) = 0#32)
    (hOut : (t &&& outMask) = 0#32) :
    ∃ n : Nat, scheduledCorrectionCount [] [j] master i
      (inputRightMask inMask d) (outputLeftBaseMask outMask d)
      L aL d t b = 2 * n := by
  rw [oneRound_count_eq_combined_mask]
  apply masked_slice_even [j] master i (inMask ||| outMask) d L aL d t b ht
  bv_decide

/-- Input and output masks observe disjoint, nontrivial base-state bits. -/
def upperInputMask : Word := 0xFFFF0000#32

def lowerOutputMask : Word :=
  0x00000FFF#32

/-- The output condition is genuinely additional: an input satisfying
    the upper-half mask may violate the lower-bit output observation. -/
theorem output_restriction_not_redundant
    (master : Master) (j : Fin 32) (L aL d : Word) :
    inputRightMask upperInputMask d
        (middleAt L aL d (d ^^^ (1#32))) ∧
    ¬ outputLeftBaseMask lowerOutputMask d
        (rightEquiv [j] master (middleAt L aL d (d ^^^ (1#32)))) := by
  constructor
  · change ((d ^^^ (1#32)) &&& upperInputMask) = (d &&& upperInputMask)
    unfold upperInputMask
    bv_decide
  · unfold outputLeftBaseMask
    rw [oneRound_leftBase]
    change ¬ (((d ^^^ (1#32)) &&& lowerOutputMask) = (d &&& lowerOutputMask))
    unfold lowerOutputMask
    bv_decide

/-- Conversely, the input condition is not implied by the output mask. -/
theorem input_restriction_not_redundant
    (master : Master) (j : Fin 32) (L aL d : Word) :
    outputLeftBaseMask lowerOutputMask d
        (rightEquiv [j] master
          (middleAt L aL d (d ^^^ (0x00010000#32)))) ∧
    ¬ inputRightMask upperInputMask d
        (middleAt L aL d (d ^^^ (0x00010000#32))) := by
  constructor
  · unfold outputLeftBaseMask
    rw [oneRound_leftBase]
    change ((d ^^^ (0x00010000#32)) &&& lowerOutputMask) =
      (d &&& lowerOutputMask)
    unfold lowerOutputMask
    bv_decide
  · change ¬ (((d ^^^ (0x00010000#32)) &&& upperInputMask) =
      (d &&& upperInputMask))
    unfold upperInputMask
    bv_decide

private theorem chosen_hides_direction_input : ((0x00006000#32) &&& upperInputMask) = 0#32 := by
  decide

private theorem chosen_hides_direction_output : ((0x00006000#32) &&& lowerOutputMask) = 0#32 := by
  decide

/-- The two witnesses from the all-key derivative obstruction satisfy
    both the input and the one-round output constraint. -/
private theorem chosen_witness_zero
    (master : Master) (j : Fin 32) (L aL d : Word) :
    admittedAt [] [j] master
      (inputRightMask upperInputMask d)
      (outputLeftBaseMask lowerOutputMask d)
      L aL d ((0#32) ^^^ d) := by
  apply (oneRound_admitted_iff master j
    upperInputMask d lowerOutputMask d L aL d ((0#32) ^^^ d)).mpr
  constructor <;> bv_decide

private theorem chosen_witness_one (master : Master) (j : Fin 32) (L aL d : Word) :
    admittedAt [] [j] master (inputRightMask upperInputMask d)
      (outputLeftBaseMask lowerOutputMask d) L aL d ((0x00001000#32) ^^^ d) := by
  apply
    (oneRound_admitted_iff master j upperInputMask d lowerOutputMask d L aL d
        ((0x00001000#32) ^^^ d)).mpr
  constructor <;> (simp only [upperInputMask, lowerOutputMask]; bv_decide)

/-- Every fixed master and every scheduled second-round key has two
    distinct positive correction fibers under the two real endpoint masks. -/
theorem chosen_two_distinct_positive_fibers
    (master : Master) (i j : Fin 32) (L aL d : Word) :
    ∃ b₀ b₁ : Word, b₀ ≠ b₁ ∧
      0 < scheduledCorrectionCount [] [j] master i
        (inputRightMask upperInputMask d)
        (outputLeftBaseMask lowerOutputMask d)
        L aL d (0x00006000#32) b₀ ∧
      0 < scheduledCorrectionCount [] [j] master i
        (inputRightMask upperInputMask d)
        (outputLeftBaseMask lowerOutputMask d)
        L aL d (0x00006000#32) b₁ := by
  exact two_positive_distinct_correction_slices [] [j] master i
    (inputRightMask upperInputMask d)
    (outputLeftBaseMask lowerOutputMask d) L aL d
    (chosen_witness_zero master j L aL d)
    (chosen_witness_one master j L aL d)

/-- No correction value occupies the whole genuinely admitted set. -/
theorem chosen_no_full_slice
    (master : Master) (i j : Fin 32) (L aL d b : Word) :
    scheduledCorrectionCount [] [j] master i
      (inputRightMask upperInputMask d)
      (outputLeftBaseMask lowerOutputMask d)
      L aL d (0x00006000#32) b <
    admittedMass [] [j] master
      (inputRightMask upperInputMask d)
      (outputLeftBaseMask lowerOutputMask d) L aL d := by
  exact strict_count_of_two_admitted_witnesses [] [j] master i
    (inputRightMask upperInputMask d)
    (outputLeftBaseMask lowerOutputMask d) L aL d b
    (chosen_witness_zero master j L aL d)
    (chosen_witness_one master j L aL d)

/-- The entire selected correction histogram is even, for any master. -/
theorem chosen_all_counts_even
    (master : Master) (i j : Fin 32) (L aL d b : Word) :
    ∃ n : Nat, scheduledCorrectionCount [] [j] master i
      (inputRightMask upperInputMask d)
      (outputLeftBaseMask lowerOutputMask d)
      L aL d (0x00006000#32) b = 2 * n := by
  exact oneRound_all_counts_even master i j upperInputMask
    lowerOutputMask L aL d (0x00006000#32) b
    (by decide) chosen_hides_direction_input chosen_hides_direction_output

end Magma.DifanScheduledCorrectionMaskedOutputs
