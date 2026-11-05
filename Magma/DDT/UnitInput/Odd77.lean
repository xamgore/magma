module

public import Magma.DDT.UnitInput.Parity
public import Magma.Differential.Core.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# The complete 77-entry unit-input DDT row for odd keys

Eight groups list 77 distinct output differences before rotation and their
exact counts. Kernel-checked carry-DP computations certify every entry.
Their positive counts sum to `2^32`, exhausting the conserved row mass;
all unlisted output differences therefore have count zero.

Rotation gives the actual RFC output coordinates. Key-parity invariance
extends the exact row and its positive support to every odd 32-bit key.
Only the explicit table and local carry counts are evaluated; full-word
sums are handled symbolically.
-/

open scoped BigOperators

namespace Magma.OddUnitInput77

open Magma.Internal Magma.GProperties Magma.CarryAutomaton
open Magma.ZeroLeft64Completeness
open Magma.UnitInputParityReduction
open Magma.MultiRoundDDT

/-- Four-state, eight-digit *exact* counting oracle. This uses the
    already proved semantic carry-DP, not the 32-bit DDT Finset. -/
private def oddDP (preRot : (V 32)) : Nat :=
  carryDPCount (wordDigits (1#32)) (wordDigits (1#32))
    (wordDigits preRot)

/-- Each entry stores (output difference before rot11, exact number of
    32-bit inputs). The group is indexed by the LAST changed nibble.
    The wraparound pair is included in group 7, not counted as a new
    distinct output difference. -/
private def level0 : List ((V 32) × Nat) := [
  (0x00000002#32, 536870912),
  (0x00000005#32, 536870912),
  (0x00000007#32, 1073741824),
  (0x00000008#32, 536870912),
  (0x0000000C#32, 536870912),
  (0x0000000E#32, 536870912)
]

private def level1 : List ((V 32) × Nat) :=
  [(0x0000001D#32, 33554432), (0x0000003D#32, 67108864), (0x0000006D#32, 33554432),
    (0x0000009D#32, 33554432), (0x000000AD#32, 100663296), (0x000000CD#32, 33554432),
    (0x000000DD#32, 67108864), (0x000000ED#32, 33554432), (0x000000FD#32, 100663296)]

private def level2 : List ((V 32) × Nat) :=
  [(0x0000039D#32, 4194304), (0x0000059D#32, 4194304), (0x0000069D#32, 6291456),
    (0x0000079D#32, 2097152), (0x0000089D#32, 4194304), (0x00000A9D#32, 2097152),
    (0x00000D9D#32, 4194304), (0x00000F9D#32, 4194304)]

private def level3 : List ((V 32) × Nat) :=
  [(0x00001B9D#32, 131072), (0x00002B9D#32, 131072), (0x00003B9D#32, 131072),
    (0x00004B9D#32, 131072), (0x00006B9D#32, 131072), (0x00007B9D#32, 262144),
    (0x00009B9D#32, 262144), (0x0000AB9D#32, 262144), (0x0000BB9D#32, 131072),
    (0x0000CB9D#32, 131072), (0x0000DB9D#32, 131072), (0x0000FB9D#32, 131072)]

private def level4 : List ((V 32) × Nat) :=
  [(0x00027B9D#32, 8192), (0x00057B9D#32, 8192), (0x00067B9D#32, 8192), (0x00077B9D#32, 8192),
    (0x00087B9D#32, 8192), (0x00097B9D#32, 16384), (0x000A7B9D#32, 16384), (0x000B7B9D#32, 8192),
    (0x000D7B9D#32, 16384), (0x000E7B9D#32, 8192), (0x000F7B9D#32, 16384)]

private def level5 : List ((V 32) × Nat) :=
  [(0x001B7B9D#32, 512), (0x002B7B9D#32, 512), (0x005B7B9D#32, 512), (0x006B7B9D#32, 512),
    (0x007B7B9D#32, 512), (0x008B7B9D#32, 512), (0x009B7B9D#32, 1024), (0x00BB7B9D#32, 512),
    (0x00CB7B9D#32, 512), (0x00DB7B9D#32, 512), (0x00EB7B9D#32, 1024), (0x00FB7B9D#32, 1024)]

private def level6 : List ((V 32) × Nat) :=
  [(0x035B7B9D#32, 64), (0x045B7B9D#32, 32), (0x065B7B9D#32, 32), (0x075B7B9D#32, 64),
    (0x085B7B9D#32, 32), (0x095B7B9D#32, 32), (0x0B5B7B9D#32, 64), (0x0C5B7B9D#32, 32),
    (0x0D5B7B9D#32, 64), (0x0F5B7B9D#32, 64)]

private def level7 : List ((V 32) × Nat) :=
  [(0x3F5B7B9D#32, 4), (0x5F5B7B9D#32, 6), (0x6F5B7B9D#32, 2), (0x7F5B7B9D#32, 4),
    (0x9F5B7B9D#32, 4), (0xBF5B7B9D#32, 4), (0xCF5B7B9D#32, 2), (0xDF5B7B9D#32, 4),
    (0xFF5B7B9D#32, 2)]

/-- All 77 entries, pairwise distinct by their first components. -/
def oddRows : List ((V 32) × Nat) :=
  level0 ++ level1 ++ level2 ++ level3 ++
  level4 ++ level5 ++ level6 ++ level7

private def certified (rows : List ((V 32) × Nat)) : Bool :=
  rows.all (fun p => decide (oddDP p.1 = p.2))

/-! The eight certificate groups are separate kernel-checked obligations.
They reduce the proved carry DP on the explicitly listed targets. -/

private theorem level0_certified : certified level0 = true := by decide +kernel

private theorem level1_certified : certified level1 = true := by decide +kernel

private theorem level2_certified : certified level2 = true := by decide +kernel

private theorem level3_certified : certified level3 = true := by decide +kernel

private theorem level4_certified : certified level4 = true := by decide +kernel

private theorem level5_certified : certified level5 = true := by decide +kernel

private theorem level6_certified : certified level6 = true := by decide +kernel

private theorem level7_certified : certified level7 = true := by decide +kernel

/-- An entry from any of the eight groups has the exact
    carry-DP count stated in the table. -/
private theorem every_row_certified (p : (V 32) × Nat)
    (hp : p ∈ oddRows) : oddDP p.1 = p.2 := by
  simp only [oddRows, List.mem_append, or_assoc] at hp
  rcases hp with h | h | h | h | h | h | h | h
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level0.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level0_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level1.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level1_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level2.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level2_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level3.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level3_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level4.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level4_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level5.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level5_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level6.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level6_certified)) p h)
  · exact of_decide_eq_true
      ((List.all_eq_true.mp (show level7.all
        (fun p => decide (oddDP p.1 = p.2)) = true from level7_certified)) p h)

/-- The real RFC `g[1]` DDT is the same 8-step DP. The target is
    deliberately specified before the eleven-bit output rotation. -/
private theorem realDDT_eq_oddDP (preRot : (V 32)) :
    xorDDT_g (1#32) (1#32) (rot11 preRot) = oddDP preRot := by
  calc
    xorDDT_g (1#32) (1#32) (rot11 preRot) =
        carryMatrixCount (wordDigits (1#32))
          (wordDigits (1#32)) (wordDigits preRot) :=
      xorDDT_g_eq_carryMatrixCount (1#32) (1#32) preRot
    _ = oddDP preRot :=
      (carryDPCount_eq_carryMatrixCount _ _ _).symm

private def rawTable : Finset ((V 32) × Nat) :=
  oddRows.toFinset

/-- The table contains 77 distinct targets. This is a closed 77-item
    check, not a computation over the 2^32 possible differences. -/
private theorem rawTable_has_77 : rawTable.card = 77 := by decide +kernel

/-- Every stored exact count is positive. -/
private theorem rawTable_positive :
    ∀ p ∈ oddRows, 0 < p.2 := by decide +kernel

/-- The 77 values exhaust the full DDT row mass. -/
private theorem rawTable_total :
    (∑ p ∈ rawTable, p.2) = 2 ^ 32 := by decide +kernel

/-- No two entries in the table claim a different count for the same
    pre-rotation output. -/
private theorem rawTable_unique :
    ∀ p ∈ oddRows, ∀ q ∈ oddRows, p.1 = q.1 → p = q := by
  decide +kernel

private theorem rawTable_inj : Set.InjOn (fun p : (V 32) × Nat => p.1) (↑rawTable) := by
  intro p hp q hq heq
  exact rawTable_unique p (List.mem_toFinset.mp hp) q (List.mem_toFinset.mp hq) heq

/-- The support before the output rotation. -/
def rawSupport : Finset (V 32) :=
  rawTable.image (fun p => p.1)

/-- Number of possible input words for a given unrotated difference,
    as an explicitly tabulated sum (at most one term is nonzero). -/
def rawReferenceCount (preRot : (V 32)) : Nat :=
  ∑ p ∈ rawTable.filter (fun p => p.1 = preRot), p.2

private def oddRawDDT (preRot : (V 32)) : Nat :=
  xorDDT_g (1#32) (1#32) (rot11 preRot)

private theorem row_member_exact (p : (V 32) × Nat) (hp : p ∈ rawTable) : oddRawDDT p.1 = p.2 := by
  change xorDDT_g (1#32) (1#32) (rot11 p.1) = p.2
  rw [realDDT_eq_oddDP]
  exact every_row_certified p (List.mem_toFinset.mp hp)

private theorem reference_member_exact (p : (V 32) × Nat) (hp : p ∈ rawTable) :
    rawReferenceCount p.1 = p.2 := by
  have hfilter : rawTable.filter (fun q => q.1 = p.1) = {p} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact rawTable_inj h.1 hp h.2
    · intro h
      subst q
      exact ⟨hp, rfl⟩
  unfold rawReferenceCount
  rw [hfilter]
  simp

private theorem reference_outside_zero (d : (V 32)) (hd : d ∉ rawSupport) :
    rawReferenceCount d = 0 := by
  have hempty : rawTable.filter (fun p => p.1 = d) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hp
    apply hd
    exact Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩
  unfold rawReferenceCount
  rw [hempty]
  simp

/-- Rotating by 11 is a bijection, independently of the nonlinear boxes. -/
private theorem rot11_injective : Function.Injective rot11 := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin 32 := ⟨j, hj⟩
  change component a i = component b i
  calc
    component a i = component (rot11 a) (i + 11) :=
      (rot11_moves_components_up a i).symm
    _ = component (rot11 b) (i + 11) :=
      congrArg (fun z : (V 32) => component z (i + 11)) h
    _ = component b i := rot11_moves_components_up b i

private noncomputable def rotationEquiv : (V 32) ≃ (V 32) :=
  Equiv.ofBijective rot11 ⟨rot11_injective, fun b => ⟨b.rotateRight 11, rot11_rotateRight11 b⟩⟩

/-- The sum of the genuine 32-bit DDT row is 2^32, proved by fibers
    and bijective reindexing; no enumeration of 32-bit words. -/
private theorem oddRaw_total_mass :
    (∑ d : (V 32), oddRawDDT d) = 2 ^ 32 := by
  have hc : Fintype.card (V 32) = 2 ^ 32 := by
    calc
      Fintype.card (V 32) = FinEnum.card (V 32) :=
        (FinEnum.card_eq_fintypeCard).symm
      _ = 2 ^ 32 := FinEnum.card_bitVec 32
  calc
    (∑ d : (V 32), oddRawDDT d) =
        ∑ out : (V 32), xorDDT_g (1#32) (1#32) out :=
      rotationEquiv.sum_comp
        (fun out => xorDDT_g (1#32) (1#32) out)
    _ = Fintype.card (V 32) :=
      xorDDT_g_sum_output (1#32) (1#32)
    _ = 2 ^ 32 := hc

/-- All of the mass 2^32 has already been verified at 77 entries. -/
private theorem oddRaw_known_mass :
    (∑ d ∈ rawSupport, oddRawDDT d) = 2 ^ 32 := by
  calc
    (∑ d ∈ rawSupport, oddRawDDT d) =
        ∑ p ∈ rawTable, oddRawDDT p.1 :=
      Finset.sum_image rawTable_inj
    _ = ∑ p ∈ rawTable, p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact row_member_exact p hp
    _ = 2 ^ 32 := rawTable_total

/-- Saturation forces all 2^32-77 other output differences to have zero
    exact DDT count. This is a theorem, not a runtime search. -/
private theorem row_outside_zero (d : (V 32))
    (hd : d ∉ rawSupport) : oddRawDDT d = 0 :=
  zero_off_saturated_subset rawSupport oddRawDDT (2 ^ 32)
    oddRaw_total_mass oddRaw_known_mass d hd

/-- MAIN RESULT 1: a complete exact reference DDT row with 77 entries.
    All other 32-bit output differences have count zero. -/
theorem odd_unit_row_raw_exact (preRot : (V 32)) :
    xorDDT_g (1#32) (1#32) (rot11 preRot) =
      rawReferenceCount preRot := by
  change oddRawDDT preRot = rawReferenceCount preRot
  by_cases hd : preRot ∈ rawSupport
  · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hd
    rw [← heq]
    rw [row_member_exact p hp, reference_member_exact p hp]
  · rw [row_outside_zero preRot hd,
        reference_outside_zero preRot hd]

/-- There are precisely 77 pre-rotation output differences. -/
theorem odd_raw_support_card : rawSupport.card = 77 := by
  calc
    rawSupport.card = rawTable.card :=
      Finset.card_image_of_injOn rawTable_inj
    _ = 77 := rawTable_has_77

/-- The public output is rotated by 11, as prescribed by RFC 8891. -/
def oddOutputSupport : Finset (V 32) := rawSupport.image rot11

theorem odd_output_support_card : oddOutputSupport.card = 77 := by
  calc
    oddOutputSupport.card = rawSupport.card :=
      Finset.card_image_of_injective rawSupport rot11_injective
    _ = 77 := odd_raw_support_card

/-- 77-entry lookup in actual output (post-rotation) coordinates. -/
def oddReferenceCount (out : (V 32)) : Nat :=
  ∑ p ∈ rawTable.filter (fun p => rot11 p.1 = out), p.2

private theorem oddReferenceCount_rot (preRot : (V 32)) :
    oddReferenceCount (rot11 preRot) = rawReferenceCount preRot := by
  have hfilter :
    rawTable.filter (fun p => rot11 p.1 = rot11 preRot) =
      rawTable.filter (fun p => p.1 = preRot) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, rot11_injective h.2⟩
    · intro h
      exact ⟨h.1, congrArg rot11 h.2⟩
  unfold oddReferenceCount rawReferenceCount
  rw [hfilter]

/-- MAIN RESULT 2: exact DDT for every (odd) first-round key, at EVERY
    possible 32-bit output difference (not only the 77 listed cases). -/
theorem odd_key_complete_DDT (k out : (V 32))
    (hk : k.toNat % 2 = 1) :
    xorDDT_g k (1#32) out = oddReferenceCount out := by
  rw [unitInput_DDT_odd_key k out hk]
  obtain ⟨preRot, hrot⟩ := rotationEquiv.surjective out
  change rot11 preRot = out at hrot
  rw [← hrot, odd_unit_row_raw_exact, oddReferenceCount_rot]

/-- The 77 tabulated values are precisely the genuine *positive*
    DDT entries, not just 77 formally listed targets. -/
private theorem rotated_mem_iff (d : (V 32)) :
    rot11 d ∈ oddOutputSupport ↔ d ∈ rawSupport := by
  constructor
  · intro h
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
    have hxd : x = d := rot11_injective heq
    simpa only [hxd] using hx
  · intro hd
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩

/-- The exact 77-element positive support for *any odd key*. -/
theorem odd_key_positive_iff_support (k out : (V 32))
    (hk : k.toNat % 2 = 1) :
    0 < xorDDT_g k (1#32) out ↔ out ∈ oddOutputSupport := by
  obtain ⟨d, heq⟩ := rotationEquiv.surjective out
  change rot11 d = out at heq
  rw [← heq, odd_key_complete_DDT k (rot11 d) hk,
    oddReferenceCount_rot, rotated_mem_iff]
  by_cases hd : d ∈ rawSupport
  · obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hd
    have hpos : 0 < rawReferenceCount d := by
      rw [← hpd, reference_member_exact p hp]
      exact rawTable_positive p (List.mem_toFinset.mp hp)
    exact ⟨fun _ => hd, fun _ => hpos⟩
  · rw [reference_outside_zero d hd]
    simp only [hd, iff_false]
    exact Nat.not_lt_zero 0

end Magma.OddUnitInput77
