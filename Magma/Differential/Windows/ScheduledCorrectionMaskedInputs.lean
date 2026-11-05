module

import all Init.Data.Range.Basic
public import Magma.Differential.Windows.ScheduledCorrectionPartnerFibers
public import Diffan.Symmetry.FiniteInvolutionOrbits
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Key-independent masked initial bases and conditional correction fibers

A mask on the initial right half of the *actual base state* is an
endpoint predicate that does not mention the key.  If the prefix is empty
and the final predicate is unrestricted, the admissible midpoint bases
are exactly a fixed mask class, for any (possibly nonempty) suffix.

If the mask does not observe the bits toggled by t, this class is closed
under R -> R XOR t.  The pointwise XOR-derivative symmetry of
`ScheduledCorrectionPartnerFibers` then pairs each correction fiber.
We prove not only a lower bound of two, but an even-cardinality theorem
using the existing general finite-involution orbit certificate.

For t=0x6000, a mask omitting bits 12, 13, 14 admits two previously
certified witnesses with distinct corrections, under every master key.
This is a genuinely key-independent input predicate, but the output
endpoint predicate is True and the prefix is empty.  It is NOT a claim
about fixed observable ciphertext endpoints or nontrivial scheduled prefixes.

-/

namespace Magma.DiffanScheduledCorrectionMaskedInputs

open Magma
open Magma.DiffanScheduledMeet
open Magma.DiffanScheduledCorrectionReachability
open Magma.DiffanScheduledCorrectionHomogeneity
open Magma.DiffanScheduledCorrectionPartnerFibers
open Magma.DiffanFeistelDeltaPropagation

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev Point :=
  Diffan.StateDifference (Word × Word) (Word × Word)

/-- Public-form endpoint condition on the actual right BASE of the
    initial state pair. No master key or round index appears here. -/
def inputRightMask (mask target : Word) (p : Point) : Prop :=
  (p.base.2 &&& mask) = (target &&& mask)

/-- The inverse of the empty scheduled prefix really is the identity
    on complete state/difference pairs. -/
theorem empty_prefix_symm (master : Master) (p : Point) :
    (leftEquiv [] master).symm p = p := by
  change Diffan.StateDifference.transport
    Magma.DiffanReverseRound.roundXor Magma.DiffanReverseRound.roundXor
    (fun x => x) p = p
  rcases p with ⟨x, a⟩
  change
    (⟨x, Diffan.derivative Magma.DiffanReverseRound.roundXor
      Magma.DiffanReverseRound.roundXor (fun y => y) a x⟩ : Point) = ⟨x, a⟩
  rw [Diffan.derivative_id]

/-- In the empty-prefix, unrestricted-suffix case the condition selects
    an ordinary mask class, not a key-dependent pullback of a midpoint. -/
theorem masked_admitted_iff
    (suffix : List (Fin 32)) (master : Master)
    (mask target L aL d R : Word) :
    admittedAt [] suffix master (inputRightMask mask target)
      (fun _ => True) L aL d R ↔
      (R &&& mask) = (target &&& mask) := by
  simp only [admittedAt, empty_prefix_symm, inputRightMask,
    middleAt, and_true]

/-- Elementary mask criterion: toggling invisible bits cannot affect
    the observation. -/
theorem masked_xor_invariant (R mask t : Word)
    (hmask : (t &&& mask) = 0#32) :
    ((R ^^^ t) &&& mask) = (R &&& mask) := by
  bv_decide

/-- The true joined midpoint condition is partner-closed for every
    master key and every suffix when the input mask hides t. -/
theorem masked_admitted_partner
    (suffix : List (Fin 32)) (master : Master)
    (mask target L aL d t R : Word)
    (hmask : (t &&& mask) = 0#32)
    (hR : admittedAt [] suffix master (inputRightMask mask target)
      (fun _ => True) L aL d R) :
    admittedAt [] suffix master (inputRightMask mask target)
      (fun _ => True) L aL d (R ^^^ t) := by
  apply (masked_admitted_iff suffix master mask target L aL d (R ^^^ t)).mpr
  rw [masked_xor_invariant R mask t hmask]
  exact (masked_admitted_iff suffix master mask target L aL d R).mp hR

/-- Every positive restricted correction count contains an entire
    XOR partner pair, even though the round key is scheduled. -/
theorem positive_masked_slice_ge_two
    (suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (mask target L aL d t b : Word)
    (ht : t ≠ 0#32) (hmask : (t &&& mask) = 0#32)
    (hpos : 0 < scheduledCorrectionCount [] suffix master i
      (inputRightMask mask target) (fun _ => True) L aL d t b) :
    2 ≤ scheduledCorrectionCount [] suffix master i
      (inputRightMask mask target) (fun _ => True) L aL d t b := by
  exact positive_slice_has_two_real_midpoints [] suffix master i
    (inputRightMask mask target) (fun _ => True) L aL d t b ht
    (fun R hR => masked_admitted_partner suffix master
      mask target L aL d t R hmask hR) hpos

/-- A finite set closed under a nonzero XOR translation splits into
    two-element orbits and therefore has even cardinality. -/
private theorem finite_partner_card_even
    (C : Finset Word) (t : Word) (ht : t ≠ 0#32)
    (hclosed : ∀ R ∈ C, R ^^^ t ∈ C) :
    ∃ n : Nat, C.card = 2 * n := by
  classical
  have ht2 (R : Word) : (R ^^^ t) ^^^ t = R := by
    bv_decide
  have hstable : C.image (fun R => R ^^^ t) = C := by
    ext R
    constructor
    · intro hh
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
      exact hclosed x hx
    · intro hR
      refine Finset.mem_image.mpr ⟨R ^^^ t, ?_, ?_⟩
      · exact hclosed R hR
      · exact ht2 R
  have hrank : ∀ R ∈ C, R.toNat ≠ (R ^^^ t).toNat := by
    intro R _ heq
    have hh : R = R ^^^ t := BitVec.toNat_injective heq
    have hz : t = 0#32 := by
      bv_decide
    exact ht hz
  refine ⟨(Diffan.FiniteInvolutionOrbits.representatives
    C (fun R => R ^^^ t) BitVec.toNat).card, ?_⟩
  exact Diffan.FiniteInvolutionOrbits.card_eq_twice_representatives
    C (fun R => R ^^^ t) BitVec.toNat ht2 hstable hrank

/-- Partner closure makes every restricted correction coefficient even,
    including the empty correction slices. -/
theorem masked_slice_even
    (suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (mask target L aL d t b : Word)
    (ht : t ≠ 0#32) (hmask : (t &&& mask) = 0#32) :
    ∃ n : Nat, scheduledCorrectionCount [] suffix master i
      (inputRightMask mask target) (fun _ => True) L aL d t b = 2 * n := by
  classical
  let C := (admittedBases [] suffix master
    (inputRightMask mask target) (fun _ => True) L aL d).filter
      (fun R => secondCorrection (roundKey master i) t (middleAt L aL d R) = b)
  have hclosed : ∀ R ∈ C, R ^^^ t ∈ C := by
    intro R hR
    obtain ⟨hA, hB⟩ := Finset.mem_filter.mp hR
    have hadm : admittedAt [] suffix master
        (inputRightMask mask target) (fun _ => True) L aL d R :=
      (mem_admittedBases [] suffix master
        (inputRightMask mask target) (fun _ => True) L aL d R).mp hA
    have hadm' := masked_admitted_partner suffix master
      mask target L aL d t R hmask hadm
    apply Finset.mem_filter.mpr
    exact ⟨(mem_admittedBases [] suffix master
      (inputRightMask mask target) (fun _ => True)
      L aL d (R ^^^ t)).mpr hadm',
      (correction_partner (roundKey master i) t L aL d R).trans hB⟩
  obtain ⟨n, hn⟩ := finite_partner_card_even C t ht hclosed
  refine ⟨n, ?_⟩
  rw [scheduledCount_as_filter]
  exact hn

/-- Hide three bits 12, 13, 14, including both bits in the partner
    direction 0x6000 and the extra bit in the obstruction witness 0x1000. -/
def threeBitHiddenMask : Word := ~~~(0x00007000#32)

private theorem threeBit_mask_hides_partner : ((0x00006000#32) &&& threeBitHiddenMask) = 0#32 := by
  decide

private theorem threeBit_witness_zero (d : Word) :
    (((0#32) ^^^ d) &&& threeBitHiddenMask) = (d &&& threeBitHiddenMask) := by bv_decide

private theorem threeBit_witness_one (d : Word) :
    (((0x00001000#32) ^^^ d) &&& threeBitHiddenMask) = (d &&& threeBitHiddenMask) := by
  unfold threeBitHiddenMask
  bv_decide

/-- A nonempty, key-independent masked initial input class has two
    genuinely different positive correction fibers for every master.
    The suffix can be any list because its endpoint condition is True.
    This does not claim fixed, observed output endpoints. -/
theorem threeBit_mask_two_distinct_positive_fibers
    (suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (L aL d : Word) :
    ∃ b₀ b₁ : Word, b₀ ≠ b₁ ∧
      0 < scheduledCorrectionCount [] suffix master i
        (inputRightMask threeBitHiddenMask d) (fun _ => True)
        L aL d (0x00006000#32) b₀ ∧
      0 < scheduledCorrectionCount [] suffix master i
        (inputRightMask threeBitHiddenMask d) (fun _ => True)
        L aL d (0x00006000#32) b₁ := by
  have h0 : admittedAt [] suffix master
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d ((0#32) ^^^ d) :=
    (masked_admitted_iff suffix master threeBitHiddenMask d L aL d
      ((0#32) ^^^ d)).mpr (threeBit_witness_zero d)
  have h1 : admittedAt [] suffix master
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d ((0x00001000#32) ^^^ d) :=
    (masked_admitted_iff suffix master threeBitHiddenMask d L aL d
      ((0x00001000#32) ^^^ d)).mpr (threeBit_witness_one d)
  exact two_positive_distinct_correction_slices [] suffix master i
    (inputRightMask threeBitHiddenMask d) (fun _ => True) L aL d h0 h1

/-- No correction value fills this entire nonempty masked midpoint
    class, uniformly over the scheduled master key. -/
theorem threeBit_mask_no_full_slice
    (suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (L aL d b : Word) :
    scheduledCorrectionCount [] suffix master i
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d (0x00006000#32) b <
    admittedMass [] suffix master
      (inputRightMask threeBitHiddenMask d) (fun _ => True) L aL d := by
  have h0 : admittedAt [] suffix master
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d ((0#32) ^^^ d) :=
    (masked_admitted_iff suffix master threeBitHiddenMask d L aL d
      ((0#32) ^^^ d)).mpr (threeBit_witness_zero d)
  have h1 : admittedAt [] suffix master
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d ((0x00001000#32) ^^^ d) :=
    (masked_admitted_iff suffix master threeBitHiddenMask d L aL d
      ((0x00001000#32) ^^^ d)).mpr (threeBit_witness_one d)
  exact strict_count_of_two_admitted_witnesses [] suffix master i
    (inputRightMask threeBitHiddenMask d) (fun _ => True) L aL d b h0 h1

/-- Specialize the even-coefficient law to a fixed, key-independent
    eight-state mask class (three unobserved bits). -/
theorem threeBit_mask_all_counts_even
    (suffix : List (Fin 32)) (master : Master) (i : Fin 32)
    (L aL d b : Word) :
    ∃ n : Nat, scheduledCorrectionCount [] suffix master i
      (inputRightMask threeBitHiddenMask d) (fun _ => True)
      L aL d (0x00006000#32) b = 2 * n := by
  apply masked_slice_even suffix master i threeBitHiddenMask d
    L aL d (0x00006000#32) b
  · decide
  · exact threeBit_mask_hides_partner

end Magma.DiffanScheduledCorrectionMaskedInputs
