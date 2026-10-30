module

import all Init.Data.Range.Basic
public import Magma.Diffan.ZeroKeyEightColumn
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Sharp six-candidate bound in the zero-second-key slice

For the slice (aR,bL,k1)=(1,0,0), a genuine intersection contains
at most ONE intermediate difference for even k0, and at most SIX for
odd k0, independently of aL and the third key. The bound six is sharp:
there are two different aL values realizing six survivors for EVERY
odd first-round key.

For c in the certified eight-column support, XOR by c changes only
nibble 5. Mask
this nibble and classify the 77 certified first-row offsets by the
remaining 28 bits: 59 singleton classes, 4 doubletons, 1 four-element
class, and 1 six-element class.

Crucial finite certificates concern only the 77 already-certified
odd-row words and their 28-bit projections. Two cardinality checks
prove injectivity on the 59 ordinary words.
-/

namespace Magma.DiffanZeroKeyEightSharpBound

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanThreeRoundCouplingDefect
open Magma.OddUnitInput77
open Magma.ZeroLeftParityCompleteSlice
open Magma.DiffanZeroKeyEightColumn
open Magma.DiffanZeroLeftSupportOverlap
open Magma.DiffanUnitColumnLow20AndUniqueEven

private abbrev Word :=
  V 32

/-- Delete only nibble 5 (bits 20 through 23), preserving 28 bits. -/
def clearNibble5 (d : Word) : Word :=
  d &&& (0xFF0FFFFF#32)

/-- The ONLY six projected values with a nontrivial fiber in the
    previously certified 77-element odd unit-input row. -/
def exceptionalMasks : Finset Word :=
  {0x0004E800#32, 0x000CE800#32,
   0x010CE800#32, 0x030CE800#32,
   0x050CE800#32, 0x060CE800#32}

/-- The 59 ordinary offsets, on which the 28-bit projection is injective. -/
def ordinaryOffsets : Finset Word :=
  oddOutputSupport.filter (fun d => clearNibble5 d ∉ exceptionalMasks)

/-- Computation only on the existing 77-entry reference support. -/
private theorem ordinaryOffsets_card : ordinaryOffsets.card = 59 := by
  decide +kernel

private theorem ordinaryMasks_card : (ordinaryOffsets.image clearNibble5).card = 59 := by
  decide +kernel

/-- Equal domain and image cardinalities certify that the ordinary
    offsets have distinct masked values. -/
theorem ordinaryMasks_injective :
    Set.InjOn clearNibble5 (↑ordinaryOffsets : Set Word) := by
  apply Finset.injOn_of_card_image_eq
  rw [ordinaryMasks_card, ordinaryOffsets_card]

/-- The whole odd-key offset fiber at a fixed 28-bit masked word. -/
def oddMaskFiber (masked : Word) : Finset Word :=
  oddOutputSupport.filter (fun d => clearNibble5 d = masked)

/-- All six exceptional fiber sizes, with the largest equal to six.
    Each check evaluates one 77-element filter, not all pairings. -/
theorem exceptional_fibers_exact :
    (oddMaskFiber (0x0004E800#32)).card = 4 ∧
    (oddMaskFiber (0x000CE800#32)).card = 6 ∧
    (oddMaskFiber (0x010CE800#32)).card = 2 ∧
    (oddMaskFiber (0x030CE800#32)).card = 2 ∧
    (oddMaskFiber (0x050CE800#32)).card = 2 ∧
    (oddMaskFiber (0x060CE800#32)).card = 2 := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · decide +kernel

/-- Away from the six exceptional projections every fiber is empty
    or singleton. The proof is symbolic using the certified injection. -/
theorem ordinary_mask_fiber_card_le_one (masked : Word)
    (hm : masked ∉ exceptionalMasks) :
    (oddMaskFiber masked).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hru, hmu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hrv, hmv⟩ := Finset.mem_filter.mp hv
  have hu' : u ∈ ordinaryOffsets :=
    Finset.mem_filter.mpr ⟨hru, by simpa only [hmu] using hm⟩
  have hv' : v ∈ ordinaryOffsets :=
    Finset.mem_filter.mpr ⟨hrv, by simpa only [hmv] using hm⟩
  exact ordinaryMasks_injective hu' hv' (hmu.trans hmv.symm)

/-- Every masked fiber contains at most six odd-key output offsets. -/
theorem odd_mask_fiber_card_le_six (masked : Word) :
    (oddMaskFiber masked).card ≤ 6 := by
  by_cases he : masked ∈ exceptionalMasks
  · simp only [exceptionalMasks, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with h | h | h | h | h | h <;> subst masked <;>
      simp only [exceptional_fibers_exact.1,
        exceptional_fibers_exact.2.1,
        exceptional_fibers_exact.2.2.1,
        exceptional_fibers_exact.2.2.2.1,
        exceptional_fibers_exact.2.2.2.2.1,
        exceptional_fibers_exact.2.2.2.2.2] <;> omega
  · have hle := ordinary_mask_fiber_card_le_one masked he
    omega

/-- XORing one of the eight supported second-round differences does
    not affect the other 28 bits of the shifted first-round offset. -/
theorem clearNibble5_xor_column (aL c : Word)
    (hc : c ∈ zeroColumnSupport) :
    clearNibble5 (xor c aL) = clearNibble5 aL := by
  rw [zeroColumnSupport_eq_literals] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h <;>
    subst c <;> unfold clearNibble5 xor <;> bv_decide

/-- For any odd k0, the surviving c-words are exactly the intersection
    between the eight-element second column and the 77-element row. -/
theorem odd_surviving_iff (k₀ aL c : Word)
    (hk : k₀.toNat % 2 = 1) :
    c ∈ survivingCandidates k₀ aL ↔
      c ∈ zeroColumnSupport ∧ xor c aL ∈ oddOutputSupport := by
  rw [survivingCandidates_iff_overlap, overlap_zeroKeySecond_iff]
  rw [odd_key_positive_iff_support k₀ (xor c aL) hk]

/-- All candidate sets are equal for any two odd first keys; this is
    a genuine whole-key-class theorem, not a sample of key values. -/
theorem odd_surviving_key_independent (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    survivingCandidates k₀ aL = survivingCandidates (1#32) aL := by
  ext c
  rw [odd_surviving_iff k₀ aL c hk,
    odd_surviving_iff (1#32) aL c (by decide)]

/-- Translation by aL is injective, so a set of compatible second-round
    c-words can be embedded without collisions into a first-row fiber. -/
private theorem xor_left_translate_injective (aL : Word) :
    Function.Injective (fun c : Word => xor c aL) := by
  intro x y h
  have hh := congrArg (fun c : Word => xor c aL) h
  change (x ^^^ aL) ^^^ aL = (y ^^^ aL) ^^^ aL at hh
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using hh

/-- The precise injection of surviving differences into one 28-bit
    class of the ODD first-round support. -/
theorem odd_surviving_image_subset_mask_fiber (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    (survivingCandidates k₀ aL).image (fun c => xor c aL) ⊆
      oddMaskFiber (clearNibble5 aL) := by
  intro d hd
  obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp hd
  obtain ⟨hcol, hrow⟩ := (odd_surviving_iff k₀ aL c hk).mp hc
  have hmask := clearNibble5_xor_column aL c hcol
  have hdm : clearNibble5 d = clearNibble5 aL := by
    rw [← hcd]
    exact hmask
  have hdr : d ∈ oddOutputSupport := by
    rw [← hcd]
    exact hrow
  exact Finset.mem_filter.mpr ⟨hdr, hdm⟩

/-- MAIN RESULT: the previous bound eight reduces sharply to six for
    arbitrary aL and ANY odd first-round key k0. -/
theorem odd_surviving_card_le_six (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1) :
    (survivingCandidates k₀ aL).card ≤ 6 := by
  calc
    (survivingCandidates k₀ aL).card =
        ((survivingCandidates k₀ aL).image
          (fun c => xor c aL)).card :=
      (Finset.card_image_of_injective _
        (xor_left_translate_injective aL)).symm
    _ ≤ (oddMaskFiber (clearNibble5 aL)).card :=
      Finset.card_le_card (odd_surviving_image_subset_mask_fiber k₀ aL hk)
    _ ≤ 6 := odd_mask_fiber_card_le_six _

/-- Outside the six EXCEPTIONAL 28-bit masks (not just six low-20
    prefixes), an odd-key overlap has at most one survivor. -/
theorem odd_surviving_card_le_one_off_masks (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 1)
    (hm : clearNibble5 aL ∉ exceptionalMasks) :
    (survivingCandidates k₀ aL).card ≤ 1 := by
  calc
    (survivingCandidates k₀ aL).card =
        ((survivingCandidates k₀ aL).image
          (fun c => xor c aL)).card :=
      (Finset.card_image_of_injective _
        (xor_left_translate_injective aL)).symm
    _ ≤ (oddMaskFiber (clearNibble5 aL)).card :=
      Finset.card_le_card (odd_surviving_image_subset_mask_fiber k₀ aL hk)
    _ ≤ 1 := ordinary_mask_fiber_card_le_one _ hm

/-- Positive three-round output outside the six projected masks always
    has ZERO defect even for odd first-round keys. -/
theorem odd_positive_defect_zero_off_masks (k₀ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hm : clearNibble5 aL ∉ exceptionalMasks)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, bR)) :
    couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR = 0 := by
  have hb : bR ∈ survivingCandidates k₀ aL :=
    (survivingCandidates_iff_overlap k₀ aL bR).mpr
      ((zeroLeftDDT_pos_iff_mem k₀ (0#32) k₂ aL (1#32) bR).mp hp)
  have honly := (Finset.card_le_one.mp
    (odd_surviving_card_le_one_off_masks k₀ aL hk hm))
  apply (couplingDefect_zero_iff_subset
    k₀ (0#32) k₂ aL (1#32) bR).mpr
  intro c hc
  have hc' : c ∈ survivingCandidates k₀ aL :=
    (survivingCandidates_iff_overlap k₀ aL c).mpr hc
  exact Set.mem_singleton_iff.mpr (honly c hc' bR hb)

/-- The EVEN first-key case is stronger: there is at most one c, as
    established earlier using the universal low-20-bit obstruction. -/
theorem even_surviving_card_le_one (k₀ aL : Word)
    (hk : k₀.toNat % 2 = 0) :
    (survivingCandidates k₀ aL).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc d hd
  exact even_overlap_unique k₀ (0#32) aL c d hk
    ((survivingCandidates_iff_overlap k₀ aL c).mp hc)
    ((survivingCandidates_iff_overlap k₀ aL d).mp hd)

/-- The key-parity-dependent sharp bound for ANY first key and left
    input difference, without iterating over any keys or left inputs. -/
theorem surviving_card_le_six (k₀ aL : Word) :
    (survivingCandidates k₀ aL).card ≤ 6 := by
  by_cases hk : k₀.toNat % 2 = 0
  · have h := even_surviving_card_le_one k₀ aL hk
    omega
  · have ho : k₀.toNat % 2 = 1 := by omega
    exact odd_surviving_card_le_six k₀ aL ho

/-- Stronger global obstruction: a selected positive three-round DDT
    coefficient can have positive defect ONLY if k0 is odd and the full
    28-bit masked aL is one of SIX exceptional values. -/
theorem positive_ddt_and_defect_forces_six_masks
    (k₀ k₂ aL bR : Word)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (aL, 1#32) (0#32, bR))
    (hd : 0 < couplingDefect k₀ (0#32) k₂ aL (1#32)
      (0#32) bR) :
    k₀.toNat % 2 = 1 ∧ clearNibble5 aL ∈ exceptionalMasks := by
  constructor
  · by_cases he : k₀.toNat % 2 = 0
    · have hz := even_defect_zero_of_positive
        k₀ (0#32) k₂ aL bR he hp
      omega
    · omega
  · by_contra hmask
    have ho : k₀.toNat % 2 = 1 := by
      by_cases he : k₀.toNat % 2 = 0
      · have hz := even_defect_zero_of_positive
          k₀ (0#32) k₂ aL bR he hp
        omega
      · omega
    have hz := odd_positive_defect_zero_off_masks
      k₀ k₂ aL bR ho hmask hp
    omega

/-- First sharpness witness: exactly SIX different c survive. -/
def sharpAL₀ : Word := 0x00ECE800#32

def sharpC₀ : Finset Word :=
  {0x00300000#32, 0x00800000#32, 0x00900000#32,
    0x00C00000#32, 0x00D00000#32, 0x00F00000#32}

/-- Second independent sharpness witness, with another six-word set. -/
def sharpAL₁ : Word := 0x00BCE800#32

def sharpC₁ : Finset Word :=
  {0x00600000#32, 0x00800000#32, 0x00900000#32,
    0x00A00000#32, 0x00C00000#32, 0x00D00000#32}

/-- Only 8 parity-row lookups against the already certified 77 table. -/
private theorem sharp₀_computed :
    survivingCandidates (1#32) sharpAL₀ = sharpC₀ := by
  decide +kernel

private theorem sharp₁_computed : survivingCandidates (1#32) sharpAL₁ = sharpC₁ := by decide +kernel

/-- ALL odd keys have the same exact six-word intersection in case 0. -/
theorem sharp₀_all_odd_keys (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    survivingCandidates k₀ sharpAL₀ = sharpC₀ := by
  rw [odd_surviving_key_independent k₀ sharpAL₀ hk]
  exact sharp₀_computed

/-- ALL odd keys have the same exact six-word intersection in case 1. -/
theorem sharp₁_all_odd_keys (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    survivingCandidates k₀ sharpAL₁ = sharpC₁ := by
  rw [odd_surviving_key_independent k₀ sharpAL₁ hk]
  exact sharp₁_computed

/-- Therefore the universal bound six cannot be improved. -/
theorem six_bound_attained (k₀ : Word)
    (hk : k₀.toNat % 2 = 1) :
    (survivingCandidates k₀ sharpAL₀).card = 6 ∧
    (survivingCandidates k₀ sharpAL₁).card = 6 := by
  rw [sharp₀_all_odd_keys k₀ hk, sharp₁_all_odd_keys k₀ hk]
  constructor <;> decide

/-- A STRICTLY POSITIVE three-round coefficient with FIVE OTHER
    intermediate contributions is now known at EVERY odd k0 and k2. -/
theorem sixfold_positive_coefficient_and_defect (k₀ k₂ : Word)
    (hk : k₀.toNat % 2 = 1) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
      (sharpAL₀, 1#32) (0#32, 0x00300000#32) ∧
    0 < couplingDefect k₀ (0#32) k₂ sharpAL₀ (1#32)
      (0#32) (0x00300000#32) := by
  have hset := sharp₀_all_odd_keys k₀ hk
  have h0 : (0x00300000#32) ∈ survivingCandidates k₀ sharpAL₀ := by
    rw [hset]
    decide
  have h1 : (0x00800000#32) ∈ survivingCandidates k₀ sharpAL₀ := by
    rw [hset]
    decide
  have hc0 := (survivingCandidates_iff_overlap
    k₀ sharpAL₀ (0x00300000#32)).mp h0
  have hc1 := (survivingCandidates_iff_overlap
    k₀ sharpAL₀ (0x00800000#32)).mp h1
  constructor
  · exact (zeroLeftDDT_pos_iff_mem
      k₀ (0#32) k₂ sharpAL₀ (1#32) (0x00300000#32)).mpr hc0
  · apply (couplingDefect_pos_iff_exists_offDiagonal
      k₀ (0#32) k₂ sharpAL₀ (1#32) (0x00300000#32)).mpr
    refine ⟨0x00800000#32, ?_, hc1⟩
    decide

end Magma.DiffanZeroKeyEightSharpBound
