module

import all Init.Data.Range.Basic
public import Magma.Differential.TwoRounds.TwoRoundSuffixObservation
import Std.Tactic.BVDecide

@[expose] public section

/-!
# A key-independent raw output mask after two ordinary Magma rounds

The preceding module recovered the original right base using the last
scheduled key. Here we instead observe ordinary output bits.

For every k, the lower twelve input bits of g[k] control the lower three
four-bit substitution boxes, independently of all higher input bits.
Rotating their output left by 11 places puts them at positions 11..22.
Hence changing x by any s whose lower twelve bits vanish cannot change
those 12 output bits of g[k]. This works for every key, not just even keys.

The left base of two ordinary G rounds is L XOR g[k_i](R). Therefore the
same fixed output mask is insensitive to R -> R XOR 0x6000, even though
the entire left output has a nonconstant response (proved previously).

A predicate on raw output bits and an independent input mask give exact
partner-closed correction fibers.
-/

namespace Magma.DiffanTwoRoundRawOutputMasks

open Magma Magma.Internal Magma.GProperties
open Magma.DiffanFeistelDeltaPropagation (secondCorrection)
open Magma.DiffanScheduledMeet
open Magma.DiffanScheduledCorrectionReachability
open Magma.DiffanScheduledCorrectionHomogeneity
open Magma.DiffanScheduledCorrectionPartnerFibers
open Magma.DiffanScheduledCorrectionMaskedInputs
open Magma.DiffanScheduledCorrectionMaskedOutputs
open Magma.DiffanTwoRoundSuffixObservation

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Diffan.StateDifference (Word × Word) (Word × Word)

/-- The three lowest S-boxes after rotation occupy bits 11..22. -/
def outputLowBoxMask : Word := 0x007FF800#32

def inputLow12Mask : Word :=
  0x00000FFF#32

/-- Only a BitVec fact: addition cannot propagate a carry downward. -/
private theorem add_preserves_low12_of_xor
    (x k s : Word) (hs : (s &&& inputLow12Mask) = 0#32) :
    (((x ^^^ s) + k) &&& inputLow12Mask) =
      ((x + k) &&& inputLow12Mask) := by
  unfold inputLow12Mask at *
  bv_decide

/-- The lower twelve bits determine exactly the first three nibbles. -/
private theorem low12_nibbles (u v : Word)
    (h : (u &&& inputLow12Mask) = (v &&& inputLow12Mask)) :
    nibble u (0 : Fin 8) = nibble v (0 : Fin 8) ∧
    nibble u (1 : Fin 8) = nibble v (1 : Fin 8) ∧
    nibble u (2 : Fin 8) = nibble v (2 : Fin 8) := by
  unfold inputLow12Mask at h
  constructor
  · change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v
    bv_decide
  constructor
  · change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v
    bv_decide
  · change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v
    bv_decide

private theorem low12_of_three_nibbles (u v : Word)
    (h0 : nibble u (0 : Fin 8) = nibble v (0 : Fin 8))
    (h1 : nibble u (1 : Fin 8) = nibble v (1 : Fin 8))
    (h2 : nibble u (2 : Fin 8) = nibble v (2 : Fin 8)) :
    (u &&& inputLow12Mask) = (v &&& inputLow12Mask) := by
  change BitVec.extractLsb' 0 4 u = BitVec.extractLsb' 0 4 v at h0
  change BitVec.extractLsb' 4 4 u = BitVec.extractLsb' 4 4 v at h1
  change BitVec.extractLsb' 8 4 u = BitVec.extractLsb' 8 4 v at h2
  unfold inputLow12Mask
  bv_decide

/-- Nibblewise substitution cannot mix the first three boxes with the rest. -/
private theorem substitution_preserves_low12 (u v : Word)
    (h : (u &&& inputLow12Mask) = (v &&& inputLow12Mask)) :
    (Magma.t u &&& inputLow12Mask) =
      (Magma.t v &&& inputLow12Mask) := by
  obtain ⟨h0, h1, h2⟩ := low12_nibbles u v h
  apply low12_of_three_nibbles (Magma.t u) (Magma.t v)
  · simpa only [t_substitutes_components] using
      congrArg (π (0 : Fin 8)) h0
  · simpa only [t_substitutes_components] using
      congrArg (π (1 : Fin 8)) h1
  · simpa only [t_substitutes_components] using
      congrArg (π (2 : Fin 8)) h2

/-- The fixed mask of the rotated output sees precisely the low twelve bits. -/
private theorem rotated_low12 (u v : Word)
    (h : (u &&& inputLow12Mask) = (v &&& inputLow12Mask)) :
    (rot11 u &&& outputLowBoxMask) =
      (rot11 v &&& outputLowBoxMask) := by
  change
    (u.rotateLeft 11 &&& (0x007FF800#32)) =
      (v.rotateLeft 11 &&& (0x007FF800#32))
  unfold inputLow12Mask at h
  bv_decide

private theorem modShift_eq_add (k x : Word) : modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [Magma.CarryAutomaton.modShift_toNat_bridge, BitVec.toNat_add]
  simp only [show (16 : Nat) ^ 8 = 2 ^ 32 from by decide]

/-- Key-independent *masked* constancy of g for every direction s which
    changes no input bits below bit 12. A full 32-bit derivative is NOT
    claimed constant. -/
theorem g_outputLowBoxMask_invariant
    (k x s : Word) (hs : (s &&& inputLow12Mask) = 0#32) :
    (g k (x ^^^ s) &&& outputLowBoxMask) =
      (g k x &&& outputLowBoxMask) := by
  have ha := add_preserves_low12_of_xor x k s hs
  have hb := substitution_preserves_low12
    ((x ^^^ s) + k) (x + k) ha
  have hc := rotated_low12
    (Magma.t ((x ^^^ s) + k)) (Magma.t (x + k)) hb
  simpa only [g_as_modShift, modShift_eq_add] using hc

/-- Masked equality is preserved by XOR with the same left input base. -/
private theorem masked_xor_right (a b L m : Word)
    (h : (a &&& m) = (b &&& m)) :
    ((a ^^^ L) &&& m) = ((b ^^^ L) &&& m) := by
  bv_decide

/-- After two ordinary scheduled rounds the raw left output base has a
    key-independent invariant observation, despite nonuniform full output. -/
theorem twoRound_leftBase_raw_mask_invariant
    (master : Master) (i j : Fin 32) (L aL d R s : Word)
    (hs : (s &&& inputLow12Mask) = 0#32) :
    (((rightEquiv [i, j] master
      (middleAt L aL d (R ^^^ s))).base.1) &&& outputLowBoxMask) =
    (((rightEquiv [i, j] master
      (middleAt L aL d R)).base.1) &&& outputLowBoxMask) := by
  simp only [twoRound_leftBase, middleAt]
  change
    ((g (roundKey master i) (R ^^^ s) ^^^ L) &&& outputLowBoxMask) =
      ((g (roundKey master i) R ^^^ L) &&& outputLowBoxMask)
  exact masked_xor_right _ _ L outputLowBoxMask
    (g_outputLowBoxMask_invariant (roundKey master i) R s hs)

/-- Exact admissibility for an ordinary mask on the two-round raw output.
    In particular the output predicate contains no round key. -/
theorem twoRound_raw_admitted_iff
    (master : Master) (i j : Fin 32)
    (inMask inTarget outTarget L aL d R : Word) :
    admittedAt [] [i, j] master
      (inputRightMask inMask inTarget)
      (outputLeftBaseMask outputLowBoxMask outTarget)
      L aL d R ↔
    (R &&& inMask) = (inTarget &&& inMask) ∧
    ((g (roundKey master i) R ^^^ L) &&& outputLowBoxMask) =
      (outTarget &&& outputLowBoxMask) := by
  change
    (inputRightMask inMask inTarget
       ((leftEquiv [] master).symm (middleAt L aL d R)) ∧
     outputLeftBaseMask outputLowBoxMask outTarget
       (rightEquiv [i, j] master (middleAt L aL d R))) ↔ _
  rw [empty_prefix_symm]
  unfold outputLeftBaseMask
  rw [twoRound_leftBase]
  rfl

/-- The raw output condition and the input condition both survive
    R -> R XOR 0x6000 for arbitrary input/output targets. -/
theorem twoRound_raw_partner_admitted
    (master : Master) (i j : Fin 32)
    (inTarget outTarget L aL d R : Word)
    (h : admittedAt [] [i, j] master
      (inputRightMask upperInputMask inTarget)
      (outputLeftBaseMask outputLowBoxMask outTarget)
      L aL d R) :
    admittedAt [] [i, j] master
      (inputRightMask upperInputMask inTarget)
      (outputLeftBaseMask outputLowBoxMask outTarget)
      L aL d (R ^^^ (0x00006000#32)) := by
  obtain ⟨hIn, hOut⟩ :=
    (twoRound_raw_admitted_iff master i j upperInputMask inTarget
      outTarget L aL d R).mp h
  apply (twoRound_raw_admitted_iff master i j upperInputMask inTarget
    outTarget L aL d (R ^^^ (0x00006000#32))).mpr
  constructor
  · rw [masked_xor_invariant R upperInputMask (0x00006000#32) (by decide)]
    exact hIn
  · have hg := g_outputLowBoxMask_invariant
      (roundKey master i) R (0x00006000#32) (by decide)
    exact (masked_xor_right _ _ L outputLowBoxMask hg).trans hOut

/-- A finite set closed under a nonzero XOR involution has even cardinality. -/
private theorem finite_partner_card_even
    (C : Finset Word) (s : Word) (hs : s ≠ 0#32)
    (hclosed : ∀ R ∈ C, R ^^^ s ∈ C) :
    ∃ n : Nat, C.card = 2 * n := by
  classical
  have hinvol (R : Word) : (R ^^^ s) ^^^ s = R := by
    bv_decide
  have hstable : C.image (fun R => R ^^^ s) = C := by
    ext R
    constructor
    · intro hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      exact hclosed x hx
    · intro hr
      exact Finset.mem_image.mpr ⟨R ^^^ s, hclosed R hr, hinvol R⟩
  have hrank : ∀ R ∈ C, R.toNat ≠ (R ^^^ s).toNat := by
    intro R _ heq
    have hh : R = R ^^^ s := BitVec.toNat_injective heq
    have hz : s = 0#32 := by bv_decide
    exact hs hz
  refine ⟨(Diffan.FiniteInvolutionOrbits.representatives
    C (fun R => R ^^^ s) BitVec.toNat).card, ?_⟩
  exact Diffan.FiniteInvolutionOrbits.card_eq_twice_representatives
    C (fun R => R ^^^ s) BitVec.toNat hinvol hstable hrank

/-- Every genuinely endpoint-restricted correction fiber is even, now
    using a mask of the raw two-round output independent of the key. -/
theorem twoRound_raw_all_counts_even
    (master : Master) (i j q : Fin 32)
    (inTarget outTarget L aL d b : Word) :
    ∃ n : Nat, scheduledCorrectionCount [] [i, j] master q
      (inputRightMask upperInputMask inTarget)
      (outputLeftBaseMask outputLowBoxMask outTarget)
      L aL d (0x00006000#32) b = 2 * n := by
  classical
  let P := inputRightMask upperInputMask inTarget
  let Q := outputLeftBaseMask outputLowBoxMask outTarget
  let C := (admittedBases [] [i, j] master P Q L aL d).filter
    (fun R => secondCorrection (roundKey master q) (0x00006000#32)
      (middleAt L aL d R) = b)
  have hclosed : ∀ R ∈ C, R ^^^ (0x00006000#32) ∈ C := by
    intro R hR
    obtain ⟨hA, hB⟩ := Finset.mem_filter.mp hR
    have hadm : admittedAt [] [i, j] master P Q L aL d R :=
      (mem_admittedBases [] [i, j] master P Q L aL d R).mp hA
    have hadm' := twoRound_raw_partner_admitted master i j
      inTarget outTarget L aL d R hadm
    apply Finset.mem_filter.mpr
    exact ⟨(mem_admittedBases [] [i, j] master P Q L aL d
      (R ^^^ (0x00006000#32))).mpr hadm',
      (correction_partner (roundKey master q) (0x00006000#32)
        L aL d R).trans hB⟩
  obtain ⟨n, hn⟩ := finite_partner_card_even C (0x00006000#32)
    (by decide) hclosed
  refine ⟨n, ?_⟩
  rw [scheduledCount_as_filter]
  exact hn

/-- Choosing a target actually realized at R=d gives a nonempty
    *raw-output* observation (although this choice of target depends on k_i). -/
private theorem selected_raw_admitted
    (master : Master) (i j : Fin 32) (L aL d s : Word)
    (hupper : (s &&& upperInputMask) = 0#32)
    (hlower : (s &&& inputLow12Mask) = 0#32) :
    admittedAt [] [i, j] master
      (inputRightMask upperInputMask d)
      (outputLeftBaseMask outputLowBoxMask
        (g (roundKey master i) d ^^^ L))
      L aL d (s ^^^ d) := by
  apply (twoRound_raw_admitted_iff master i j upperInputMask d
    (g (roundKey master i) d ^^^ L) L aL d (s ^^^ d)).mpr
  constructor
  · change ((s ^^^ d) &&& upperInputMask) = (d &&& upperInputMask)
    bv_decide
  · have hs : s ^^^ d = d ^^^ s := BitVec.xor_comm s d
    rw [hs]
    exact masked_xor_right _ _ L outputLowBoxMask
      (g_outputLowBoxMask_invariant (roundKey master i) d s hlower)

/-- Two unequal correction values occur on actual admitted states with
    an ordinary two-round output mask. No last-round key is used to decode
    the output observation; only the target is chosen from a witness. -/
theorem selected_raw_two_positive_corrections
    (master : Master) (i j q : Fin 32) (L aL d : Word) :
    ∃ b₀ b₁ : Word, b₀ ≠ b₁ ∧
      0 < scheduledCorrectionCount [] [i, j] master q
        (inputRightMask upperInputMask d)
        (outputLeftBaseMask outputLowBoxMask
          (g (roundKey master i) d ^^^ L))
        L aL d (0x00006000#32) b₀ ∧
      0 < scheduledCorrectionCount [] [i, j] master q
        (inputRightMask upperInputMask d)
        (outputLeftBaseMask outputLowBoxMask
          (g (roundKey master i) d ^^^ L))
        L aL d (0x00006000#32) b₁ := by
  exact two_positive_distinct_correction_slices [] [i, j] master q
    (inputRightMask upperInputMask d)
    (outputLeftBaseMask outputLowBoxMask
      (g (roundKey master i) d ^^^ L)) L aL d
    (selected_raw_admitted master i j L aL d (0#32)
      (by decide) (by decide))
    (selected_raw_admitted master i j L aL d (0x00001000#32)
      (by decide) (by decide))

end Magma.DiffanTwoRoundRawOutputMasks
