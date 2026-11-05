module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.ZeroKeySingletonOverlap
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Low-twenty-bit obstruction and singleton support for even first keys

This is a structural extension of the certified zero-key 64-pair table.
For every round-function key k, D_g[k](d,1)>0 implies that the least
significant twenty bits of d are zero. The proof uses: 11-bit rotation,
injectivity of the first five nibble substitutions, and cancellation of
modular addition on the low 20 bits.

For aR=1, an even first key has eight known DDT row offsets, all smaller
than 2^20 and therefore distinct after low-20 truncation. Intersecting
that row (shifted by aL) with any second-key column ending at output 1
therefore yields at most one intermediate difference. As a result,
every positive coefficient in this particular three-round slice has
zero off-diagonal coupling defect, for arbitrary second and third keys.
-/

namespace Magma.DifanUnitColumnLow20AndUniqueEven

open Magma
open Magma.Internal
open Magma.GProperties
open Magma.CarryAutomaton
open Magma.MultiRoundDDT
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanEvenUnitOverlapEight
open Magma.ZeroLeftParityCompleteSlice
open Magma.ZeroLeftEightEntries
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

/-- The least significant twenty bits of a word. -/
def low20 (x : Word) : V 20 := BitVec.extractLsb' 0 20 x

/-- Five low nibble equalities imply equality of the low twenty bits. -/
private theorem low20_of_five_nibbles (u v : Word)
    (h : ∀ i : Fin 5,
      nibble u ⟨i.val, by omega⟩ = nibble v ⟨i.val, by omega⟩) :
    low20 u = low20 v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [nibble, substring] at h0 h1 h2 h3 h4
  unfold low20
  bv_decide

/-- XOR-equality to zero forces two 4-bit substituted values equal. -/
private theorem digit_xor_zero (u v : V 4)
    (h : xor u v = (0#4)) : u = v := by
  change u ^^^ v = 0#4 at h
  bv_decide

/-- Ordinary BitVec addition implements the existing modular translation. -/
private theorem modShift_eq_add (k x : Word) : modShift k x = x + k := by
  apply BitVec.eq_of_toNat_eq
  rw [modShift_toNat_bridge, BitVec.toNat_add]
  simp only [show (16 : Nat) ^ 8 = 2 ^ 32 from by decide]

/-- Pointwise structural obstruction for an output difference of 1.
    The input XOR-difference cannot touch any of its low twenty bits. -/
theorem unit_output_forces_low20_zero (k d x : Word)
    (h : xor (g k (xor x d)) (g k x) = (1#32)) :
    low20 d = (0#20) := by
  have hrot : rot11 (0x00200000#32) = (1#32) := by decide
  have hlocal :=
    (g_xor_difference_iff_nibbles k d (0x00200000#32) x).mp
      (by simpa only [hrot] using h)
  have hn : ∀ i : Fin 5,
      nibble (modShift k (xor x d)) ⟨i.val, by omega⟩ =
        nibble (modShift k x) ⟨i.val, by omega⟩ := by
    intro i
    let j : Fin 8 := ⟨i.val, by omega⟩
    have hout : nibble (0x00200000#32) j = (0#4) := by
      fin_cases i <;> decide
    have hh := hlocal j
    rw [hout] at hh
    have hs := digit_xor_zero _ _ hh
    exact (π_is_bijective j).injective hs
  have hl := low20_of_five_nibbles _ _ hn
  rw [modShift_eq_add, modShift_eq_add] at hl
  change BitVec.extractLsb' 0 20 (xor x d + k) =
    BitVec.extractLsb' 0 20 (x + k) at hl
  rw [BitVec.extractLsb'_add (by decide : 20 ≤ 32),
      BitVec.extractLsb'_add (by decide : 20 ≤ 32)] at hl
  have hcancel : low20 (xor x d) = low20 x := by
    change low20 (xor x d) + low20 k = low20 x + low20 k at hl
    have hsub := congrArg (fun z : V 20 => z - low20 k) hl
    simpa only [BitVec.add_sub_cancel] using hsub
  unfold low20 at hcancel ⊢
  change BitVec.extractLsb' 0 20 (x ^^^ d) =
    BitVec.extractLsb' 0 20 x at hcancel
  bv_decide

/-- The global full-word DDT support obstruction, for any key and any
    input XOR-difference, not only OneHot differences. -/
theorem unit_column_positive_low20_zero (k d : Word)
    (hp : 0 < xorDDT_g k d (1#32)) :
    low20 d = (0#20) := by
  unfold xorDDT_g at hp
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
  have hdiff := (Finset.mem_filter.mp hx).2
  exact unit_output_forces_low20_zero k d x hdiff

/-- The contrapositive supplies a whole family of zero DDT entries. -/
theorem unit_column_zero_of_low20_nonzero (k d : Word)
    (hd : low20 d ≠ (0#20)) :
    xorDDT_g k d (1#32) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hd (unit_column_positive_low20_zero k d hp)

/-- The eight certified offsets are determined by their low twenty bits. -/
private theorem offset_lt_20 (d : Word) (hd : d ∈ eightOffsets) :
    d.toNat < 2 ^ 20 := by
  simp only [eightOffsets, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h | h | h | h | h <;> subst d <;> decide

/-- Low-20-bit extraction is injective ON the finite eight-offset set. -/
private theorem offset_low20_injective (u v : Word)
    (hu : u ∈ eightOffsets) (hv : v ∈ eightOffsets)
    (h : low20 u = low20 v) : u = v := by
  have hnat := congrArg BitVec.toNat h
  have hnorm (w : Word) (hw : w ∈ eightOffsets) :
      (low20 w).toNat = w.toNat := by
    unfold low20
    rw [BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_zero]
    exact Nat.mod_eq_of_lt (offset_lt_20 w hw)
  rw [hnorm u hu, hnorm v hv] at hnat
  exact BitVec.eq_of_toNat_eq hnat

/-- On the eight shifted offsets, low-20 equality forces equality of
    the full candidate differences (XOR translation is injective). -/
private theorem candidate_unique (aL c₁ c₂ : Word)
    (hc₁ : c₁ ∈ eightCandidates aL)
    (hc₂ : c₂ ∈ eightCandidates aL)
    (h₁ : low20 c₁ = (0#20)) (h₂ : low20 c₂ = (0#20)) :
    c₁ = c₂ := by
  have hmem₁ := (mem_eightCandidates_iff aL c₁).mp hc₁
  have hmem₂ := (mem_eightCandidates_iff aL c₂).mp hc₂
  have hlo : low20 (xor c₁ aL) = low20 (xor c₂ aL) := by
    unfold low20 at *
    unfold xor
    bv_decide
  have hh := offset_low20_injective _ _ hmem₁ hmem₂ hlo
  have hh' := congrArg (fun z : Word => xor z aL) hh
  change (c₁ ^^^ aL) ^^^ aL = (c₂ ^^^ aL) ^^^ aL at hh'
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    using hh'

/-- For arbitrary second key and left input difference, the support
    overlap with unit right input and even first key has at most one member. -/
theorem even_overlap_unique (k₀ k₁ aL c d : Word)
    (hk : k₀.toNat % 2 = 0)
    (hc : c ∈ supportOverlap k₀ k₁ aL (1#32))
    (hd : d ∈ supportOverlap k₀ k₁ aL (1#32)) :
    c = d := by
  obtain ⟨hC, hD⟩ := (even_overlap_mem_iff k₀ k₁ aL c hk).mp hc
  obtain ⟨hC', hD'⟩ := (even_overlap_mem_iff k₀ k₁ aL d hk).mp hd
  exact candidate_unique aL c d hC hC'
    (unit_column_positive_low20_zero k₁ c hD)
    (unit_column_positive_low20_zero k₁ d hD')

/-- Every positive target bR necessarily equals the UNIQUE overlap
    candidate. Thus the full coupling defect is zero. -/
theorem even_defect_zero_of_positive
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 0)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    couplingDefect k₀ k₁ k₂ aL (1#32) (0#32) bR = 0 := by
  have hb : bR ∈ supportOverlap k₀ k₁ aL (1#32) :=
    (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL (1#32) bR).mp hp
  apply (couplingDefect_zero_iff_subset k₀ k₁ k₂ aL (1#32) bR).mpr
  intro c hc
  exact Set.mem_singleton_iff.mpr (even_overlap_unique k₀ k₁ aL c bR hk hc hb)

/-- A positive three-round target identifies the whole support overlap. -/
theorem even_overlap_singleton_of_positive
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 0)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    supportOverlap k₀ k₁ aL (1#32) = ({bR} : Set Word) := by
  have hb : bR ∈ supportOverlap k₀ k₁ aL (1#32) :=
    (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL (1#32) bR).mp hp
  apply Set.Subset.antisymm
  · intro c hc
    exact Set.mem_singleton_iff.mpr
      (even_overlap_unique k₀ k₁ aL c bR hk hc hb)
  · intro c hc
    have heq := Set.mem_singleton_iff.mp hc
    subst c
    exact hb

/-- Any positive coefficient in this even-first-key zero-left slice
    forces the low-20 prefix of aL to equal one of the EIGHT offsets. -/
theorem even_positive_requires_eight_low20_offsets
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 0)
    (hp : 0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR)) :
    ∃ d ∈ eightOffsets, low20 aL = low20 d := by
  have hb : bR ∈ supportOverlap k₀ k₁ aL (1#32) :=
    (zeroLeftDDT_pos_iff_mem k₀ k₁ k₂ aL (1#32) bR).mp hp
  obtain ⟨hc, hz⟩ := (even_overlap_mem_iff k₀ k₁ aL bR hk).mp hb
  refine ⟨xor bR aL, (mem_eightCandidates_iff aL bR).mp hc, ?_⟩
  have hb20 := unit_column_positive_low20_zero k₁ bR hz
  unfold low20 at *
  unfold xor
  bv_decide

/-- A key-independent impossibility criterion for this slice:
    if the low 20 bits of aL fail all eight certified offsets, then
    EVERY requested bR has zero three-round DDT coefficient. -/
theorem even_zero_of_no_matching_low20
    (k₀ k₁ k₂ aL bR : Word)
    (hk : k₀.toNat % 2 = 0)
    (h : ∀ d ∈ eightOffsets, low20 aL ≠ low20 d) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  obtain ⟨d, hd, heq⟩ :=
    even_positive_requires_eight_low20_offsets k₀ k₁ k₂ aL bR hk hp
  exact h d hd heq

end Magma.DifanUnitColumnLow20AndUniqueEven
