module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.UnitColumnLow20AndUniqueEven
public import Magma.DDT.ZeroLeft.ParityCompleteSlice
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Six exceptional low-twenty-bit prefixes of odd unit-input rows

For odd first key k0, the complete 77-element support of D_g[k0](1,-)
was certified earlier. Its low-20 projection has 42 values. Just six
values occur more than once; the largest fiber has 29 elements.

For any second key k1, D_g[k1](c,1)>0 forces low20(c)=0. Hence a shifted
77-element row can intersect that column at multiple points ONLY if
low20(aL) is one of the six explicitly certified collision prefixes.

Thus all positive zero-left three-round DDT entries outside those six
prefixes have zero coupling defect, even when the first key is odd.
-/

namespace Magma.DifanOddUnitLow20CollisionClasses

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OddUnitInput77
open Magma.ZeroLeftParityCompleteSlice
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanUnitColumnLow20AndUniqueEven
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- Precisely those low-20 prefixes that occur at least twice in
    the existing 77-entry odd-key output support. -/
def oddCollisionPrefixes : Finset (V 20) :=
  {0x0004E800#20, 0x000CE800#20,
   0x000CE803#20, 0x000CE804#20,
   0x000CE806#20, 0x000CE807#20}

/-- All possible low-20 prefixes from the 77-item odd support. -/
def oddPossiblePrefixes : Finset (V 20) :=
  oddOutputSupport.image low20

/-- A closed 77-element check: 42 different low-20 prefixes. -/
theorem odd_possible_prefixes_card : oddPossiblePrefixes.card = 42 := by
  decide +kernel

/-- The six exceptional prefixes are distinct. -/
theorem odd_collision_prefixes_card : oddCollisionPrefixes.card = 6 := by
  decide

/-- How many certified odd-key offsets have a particular low-20 prefix? -/
def oddPrefixMultiplicity (p : V 20) : Nat :=
  (oddOutputSupport.filter (fun d => low20 d = p)).card

/-- The largest bucket contains 29 already-certified words. -/
theorem odd_bucket29_exact :
    oddPrefixMultiplicity (0x000CE800#20) = 29 := by
  decide +kernel

/-- Odd-key output offsets whose low twenty bits avoid the collision classes. -/
private def oddNoncollisionOffsets : Finset Word :=
  oddOutputSupport.filter (fun d => low20 d ∉ oddCollisionPrefixes)

private theorem odd_noncollision_offsets_card : oddNoncollisionOffsets.card = 36 := by
  decide +kernel

private theorem odd_noncollision_image_card : (oddNoncollisionOffsets.image low20).card = 36 := by
  decide +kernel

/-- Equal domain and image sizes certify that the nonexceptional offsets
    have distinct low-twenty-bit projections. -/
private theorem odd_noncollision_low20_injective :
    Set.InjOn low20 oddNoncollisionOffsets := by
  apply Finset.injOn_of_card_image_eq
  rw [odd_noncollision_image_card, odd_noncollision_offsets_card]

/-- Distinct offsets share low twenty bits only at a collision prefix. -/
theorem odd_collision_covered
    (u v : Word) (hu : u ∈ oddOutputSupport)
    (hv : v ∈ oddOutputSupport)
    (heq : low20 u = low20 v) :
    u = v ∨ low20 u ∈ oddCollisionPrefixes := by
  by_cases hbad : low20 u ∈ oddCollisionPrefixes
  · exact Or.inr hbad
  · left
    have hvbad : low20 v ∉ oddCollisionPrefixes := by
      rw [← heq]
      exact hbad
    exact odd_noncollision_low20_injective
      (Finset.mem_filter.mpr ⟨hu, hbad⟩)
      (Finset.mem_filter.mpr ⟨hv, hvbad⟩) heq

/-- Outside the six collision prefixes, a finite support fiber
    contains at most one 32-bit output difference. -/
theorem odd_prefix_unique_off_collisions
    (p : V 20) (hp : p ∉ oddCollisionPrefixes) :
    oddPrefixMultiplicity p ≤ 1 := by
  unfold oddPrefixMultiplicity
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hu, hpu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv, hpv⟩ := Finset.mem_filter.mp hv
  rcases odd_collision_covered u v hu hv (hpu.trans hpv.symm) with heq | hbad
  · exact heq
  · exact False.elim (hp (hpu ▸ hbad))

/-- Even the largest odd-key support fiber has at most 29 entries.
    For the six exceptional values, the bound is a small, closed
    table computation. Everywhere else it follows symbolically. -/
theorem odd_prefix_multiplicity_le29 (p : V 20) :
    oddPrefixMultiplicity p ≤ 29 := by
  by_cases hp : p ∈ oddCollisionPrefixes
  · simp only [oddCollisionPrefixes, Finset.mem_insert,
      Finset.mem_singleton] at hp
    rcases hp with h | h | h | h | h | h <;> subst p <;> decide +kernel
  · have hle := odd_prefix_unique_off_collisions p hp
    omega

/-- Exactly 36 of the 42 supported prefixes are nonexceptional. -/
theorem odd_noncollision_prefixes_card :
    (oddPossiblePrefixes \ oddCollisionPrefixes).card = 36 := by
  decide +kernel

/-- The most that can survive the universal low20 column obstruction
    is 29 first-round output offsets (before applying second-key tests). -/
def oddPotentialOffsets (aL : Word) : Finset Word :=
  oddOutputSupport.filter (fun d => low20 d = low20 aL)

theorem odd_potential_offsets_card_le29 (aL : Word) : (oddPotentialOffsets aL).card ≤ 29 :=
  odd_prefix_multiplicity_le29 (low20 aL)

/-- At odd k0, shifted row membership is membership in the previously
    certified 77-element support, for EVERY odd 32-bit key. -/
theorem odd_overlap_mem_iff (k₀ k₁ aL c : Word)
    (hk : k₀.toNat % 2 = 1) :
    c ∈ supportOverlap k₀ k₁ aL (1#32) ↔
      xor c aL ∈ oddOutputSupport ∧ 0 < xorDDT_g k₁ c (1#32) := by
  change (0 < xorDDT_g k₀ (1#32) (xor c aL) ∧
    0 < xorDDT_g k₁ c (1#32)) ↔ _
  rw [odd_key_positive_iff_support k₀ (xor c aL) hk]

/-- A unit-output column forces low20(c)=0; hence the low20 prefix
    of every shifted odd-key row member equals low20(aL). -/
private theorem shift_prefix_of_col_positive
    (k₁ aL c : Word) (hc : 0 < xorDDT_g k₁ c (1#32)) :
    low20 (xor c aL) = low20 aL := by
  have hz := unit_column_positive_low20_zero k₁ c hc
  unfold low20 at *
  unfold xor
  bv_decide

/-- A purely finite superset of all possible intermediate c words.
    It is built from at most 29 entries of the certified odd output row. -/
def oddPotentialCandidates (aL : Word) : Finset Word :=
  (oddPotentialOffsets aL).image (fun d => xor d aL)

private theorem xor_translate_injective (aL : Word) :
    Function.Injective (fun d : Word => xor d aL) := by
  intro u v h
  have ht := congrArg (fun z : Word => xor z aL) h
  change (u ^^^ aL) ^^^ aL = (v ^^^ aL) ^^^ aL at ht
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using ht

theorem odd_potential_candidates_card_le29 (aL : Word) : (oddPotentialCandidates aL).card ≤ 29 := by
  unfold oddPotentialCandidates
  rw [Finset.card_image_of_injective _ (xor_translate_injective aL)]
  exact odd_potential_offsets_card_le29 aL

/-- No compatible c lies outside this small, key-independent candidate set. -/
theorem odd_overlap_subset_candidates
    (k₀ k₁ aL c : Word) (hk : k₀.toNat % 2 = 1)
    (hc : c ∈ supportOverlap k₀ k₁ aL (1#32)) :
    c ∈ oddPotentialCandidates aL := by
  obtain ⟨hr, hd⟩ := (odd_overlap_mem_iff k₀ k₁ aL c hk).mp hc
  have hp := shift_prefix_of_col_positive k₁ aL c hd
  apply Finset.mem_image.mpr
  refine ⟨xor c aL, Finset.mem_filter.mpr ⟨hr, hp⟩, ?_⟩
  change (c ^^^ aL) ^^^ aL = c
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Away from the six exceptional prefixes, two compatible odd-key
    candidates MUST be the same. The second key remains arbitrary. -/
theorem odd_overlap_unique_off_collisions
    (k₀ k₁ aL c d : Word)
    (hk : k₀.toNat % 2 = 1)
    (hprefix : low20 aL ∉ oddCollisionPrefixes)
    (hc : c ∈ supportOverlap k₀ k₁ aL (1#32))
    (hd : d ∈ supportOverlap k₀ k₁ aL (1#32)) :
    c = d := by
  obtain ⟨hrowc, hcolc⟩ := (odd_overlap_mem_iff k₀ k₁ aL c hk).mp hc
  obtain ⟨hrowd, hcold⟩ := (odd_overlap_mem_iff k₀ k₁ aL d hk).mp hd
  have hprefixc := shift_prefix_of_col_positive k₁ aL c hcolc
  have hprefixd := shift_prefix_of_col_positive k₁ aL d hcold
  have hpair := odd_collision_covered (xor c aL) (xor d aL)
    hrowc hrowd (hprefixc.trans hprefixd.symm)
  have heq : xor c aL = xor d aL := by
    rcases hpair with heq | hex
    · exact heq
    · exact False.elim (hprefix (hprefixc ▸ hex))
  have hcancel := congrArg (fun x : Word => xor x aL) heq
  change (c ^^^ aL) ^^^ aL = (d ^^^ aL) ^^^ aL at hcancel
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    using hcancel

/-- For an odd first key, positive selected outputs outside the six
    collision prefixes have zero coupling defect. -/
theorem odd_defect_zero_of_positive_off_collisions
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hprefix : low20 aL ∉ oddCollisionPrefixes)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR = 0 := by
  have hb : bR ∈ supportOverlap k₀ k₁ aL (1#32) :=
    (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL (1#32) bR).mp hp
  apply (couplingDefect_zero_iff_subset k₀ k₁ k₂ aL (1#32) bR).mpr
  intro c hc
  exact Set.mem_singleton_iff.mpr
    (odd_overlap_unique_off_collisions k₀ k₁ aL c bR
      hk hprefix hc hb)

/-- Outside the six collision prefixes, a positive DDT entry has zero
    coupling defect for either parity of the first key. -/
theorem defect_zero_of_positive_off_collisions
    (k₀ k₁ k₂ aL bR : Word)
    (hprefix : low20 aL ∉ oddCollisionPrefixes)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR = 0 := by
  by_cases he : k₀.toNat % 2 = 0
  · exact even_defect_zero_of_positive k₀ k₁ k₂ aL bR he hp
  · have ho : k₀.toNat % 2 = 1 := by omega
    exact odd_defect_zero_of_positive_off_collisions
      k₀ k₁ k₂ aL bR ho hprefix hp

/-- Necessary condition for a POSITIVE three-round DDT coefficient
    to have POSITIVE defect: low20(aL) is one of just six words.
    Note that positivity of the defect ALONE does not suffice: choosing
    the wrong bR can put a single supported term off diagonal. -/
theorem positive_ddt_and_defect_forces_collision_prefix
    (k₀ k₁ k₂ aL bR : Word)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR))
    (hd : 0 < couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR) :
    low20 aL ∈ oddCollisionPrefixes := by
  by_contra hprefix
  have hz := defect_zero_of_positive_off_collisions
    k₀ k₁ k₂ aL bR hprefix hp
  omega

/-- Sharpened obstruction: simultaneous positive DDT and positive
    defect requires BOTH odd first-key parity and one of six prefixes. -/
theorem positive_ddt_and_defect_requires_odd_collision
    (k₀ k₁ k₂ aL bR : Word)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR))
    (hd : 0 < couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR) :
    k₀.toNat % 2 = 1 ∧ low20 aL ∈ oddCollisionPrefixes := by
  constructor
  · by_cases he : k₀.toNat % 2 = 0
    · have hz := even_defect_zero_of_positive k₀ k₁ k₂ aL bR he hp
      omega
    · omega
  · exact positive_ddt_and_defect_forces_collision_prefix
      k₀ k₁ k₂ aL bR hp hd

/-- Nonempty odd-key support intersection constrains the low20 prefix
    of aL to one of the 42 listed values (rather than all 2^20). -/
theorem odd_positive_requires_42_prefixes
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    low20 aL ∈ oddPossiblePrefixes := by
  have hb : bR ∈ supportOverlap k₀ k₁ aL (1#32) :=
    (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL (1#32) bR).mp hp
  obtain ⟨hr, hc⟩ := (odd_overlap_mem_iff k₀ k₁ aL bR hk).mp hb
  exact Finset.mem_image.mpr
    ⟨xor bR aL, hr, shift_prefix_of_col_positive k₁ aL bR hc⟩

/-- Universal elimination of all inputs whose low20 prefix does not
    occur among the 42 supports for any odd first key. -/
theorem odd_zero_of_prefix_not_supported
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 1)
    (h : low20 aL ∉ oddPossiblePrefixes) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact h (odd_positive_requires_42_prefixes k₀ k₁ k₂ aL bR hk hp)

end Magma.DifanOddUnitLow20CollisionClasses
