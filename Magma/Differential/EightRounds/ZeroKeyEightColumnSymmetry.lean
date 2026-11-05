module

import all Init.Data.Range.Basic
public import Magma.Differential.EightRounds.ZeroKeyEightDefectSpectrum
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Symbolic XOR stabilizer of the zero-key eight-column

The 76-pair symmetry of `ZeroKeyEightDefectSpectrum` is not an accident
of the odd 77-entry row.  The eight-element column C itself is stable
under translation by 0x00500000.  Hence, FOR EVERY row weight function
r : V 32 → Nat, translating both the left difference and the selected
middle difference leaves the convolution mass, selected weight, and
excluded-diagonal defect unchanged.

Moreover, the column has no other nontrivial XOR translations: any
stabilizer must be an XOR of two elements of C, leaving at most 8*8
finite candidates.  The only stabilizers are 0 and 0x00500000.

The invariance laws hold for arbitrary row weight functions. The finite
certificates establish column stability and classify the shifts among
the XOR differences of its eight elements.
-/

namespace Magma.DifanZeroKeyEightColumnSymmetry

open Magma
open Magma.MultiRoundDDT
open Magma.DifanZeroLeftSupportOverlap
open Magma.ZeroLeftParityCompleteSlice
open Magma.DifanThreeRoundCouplingDefect
open Magma.DifanZeroKeyEightColumn
open Magma.DifanZeroKeyEightDefectWeights
open Magma.DifanZeroKeyEightDefectSpectrum

private abbrev Word :=
  V 32

/-- The unique nonzero XOR translation preserving the eight-word column. -/
def translation : Word := pairShiftMask

def translate (x : Word) : Word :=
  xor x translation

theorem translate_involutive (x : Word) : translate (translate x) = x := by
  unfold translate xor
  bv_decide

theorem translate_injective : Function.Injective translate := by
  intro x y h
  have hh := congrArg translate h
  simpa only [translate_involutive] using hh

theorem xor_translate_right (x y : Word) : xor x (translate y) = xor (translate x) y := by
  unfold translate xor
  bv_decide

theorem xor_translate_both (x y : Word) : xor (translate x) (translate y) = xor x y := by
  unfold translate xor
  bv_decide

/-- The sole S-box-specific eight-element certificate needed for all
    the symbolic invariance proofs below. -/
theorem column_stable :
    zeroColumnSupport.image translate = zeroColumnSupport := by
  decide +kernel

theorem translate_mem_column_iff (c : Word) :
    translate c ∈ zeroColumnSupport ↔ c ∈ zeroColumnSupport := by
  have forward (x : Word) (hx : x ∈ zeroColumnSupport) : translate x ∈ zeroColumnSupport := by
    rw [← column_stable]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  constructor
  · intro hc
    have hh := forward (translate c) hc
    simpa only [translate_involutive] using hh
  · exact forward c

/-! ## Classification of XOR stabilizers -/

/-- If C XOR t = C, then t is a difference between two members of C. -/
def translationCandidates : Finset Word :=
  (zeroColumnSupport.product zeroColumnSupport).image
    (fun p : Word × Word => xor p.1 p.2)

def columnStabilizers : Finset Word :=
  translationCandidates.filter
    (fun t => zeroColumnSupport.image (fun c => xor c t) = zeroColumnSupport)

theorem stabilizer_mem_candidates (t : Word)
    (h : zeroColumnSupport.image (fun c => xor c t) = zeroColumnSupport) :
    t ∈ translationCandidates := by
  have hbase : (0x00300000#32) ∈ zeroColumnSupport := by decide +kernel
  have hm : xor (0x00300000#32) t ∈ zeroColumnSupport := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨0x00300000#32, hbase, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨(0x00300000#32, xor (0x00300000#32) t), Finset.mem_product.mpr ⟨hbase, hm⟩, ?_⟩
  change xor (0x00300000#32) (xor (0x00300000#32) t) = t
  unfold xor
  bv_decide

/-- A finite certificate over at most 64 candidate shifts. -/
theorem columnStabilizers_exact :
    columnStabilizers = ({0#32, 0x00500000#32} : Finset Word) := by
  decide +kernel

/-- Full classification, for any 32-bit shift t; the left-hand side
    quantifies over the whole column, but the proof does not. -/
theorem column_stabilizer_iff (t : Word) :
    zeroColumnSupport.image (fun c => xor c t) = zeroColumnSupport ↔
      t = (0#32) ∨ t = (0x00500000#32) := by
  constructor
  · intro h
    have hc : t ∈ columnStabilizers :=
      Finset.mem_filter.mpr ⟨stabilizer_mem_candidates t h, h⟩
    rw [columnStabilizers_exact] at hc
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  · rintro (hzero | hnonzero)
    · subst t
      decide +kernel
    · subst t
      change zeroColumnSupport.image translate = zeroColumnSupport
      exact column_stable

/-! ## Generic weighted-column laws (no Magma DDT property required) -/

/-- Any weight function on a 32-bit row can be used. -/
def rowMass (row : Word → Nat) (aL : Word) : Nat :=
  ∑ c ∈ zeroColumnSupport, row (xor c aL)

def rowSelected (row : Word → Nat) (aL bR : Word) : Nat :=
  if bR ∈ zeroColumnSupport then row (xor bR aL) else 0

def rowDefect (row : Word → Nat) (aL bR : Word) : Nat :=
  ∑ c ∈ zeroColumnSupport.erase bR, row (xor c aL)

/-- A finite-set reindexing, applicable to an arbitrary weight function. -/
private theorem sum_translate (f : Word → Nat) :
    (∑ c ∈ zeroColumnSupport, f (translate c)) =
      ∑ c ∈ zeroColumnSupport, f c := by
  have hinj : Set.InjOn translate (↑zeroColumnSupport) :=
    fun _ _ _ _ hxy => translate_injective hxy
  have hsum :
      (∑ c ∈ zeroColumnSupport.image translate, f c) =
        ∑ c ∈ zeroColumnSupport, f (translate c) :=
    Finset.sum_image hinj
  rw [← hsum, column_stable]

/-- Entire eight-term mass is invariant for EVERY row and left input. -/
theorem rowMass_translate (row : Word → Nat) (aL : Word) :
    rowMass row (translate aL) = rowMass row aL := by
  unfold rowMass
  calc
    (∑ c ∈ zeroColumnSupport, row (xor c (translate aL))) =
        ∑ c ∈ zeroColumnSupport, row (xor (translate c) aL) := by
          apply Finset.sum_congr rfl
          intro c _
          exact congrArg row (xor_translate_right c aL)
    _ = ∑ c ∈ zeroColumnSupport, row (xor c aL) :=
      sum_translate (fun c => row (xor c aL))

/-- A selected coefficient is preserved by translating BOTH indices. -/
theorem rowSelected_translate (row : Word → Nat) (aL bR : Word) :
    rowSelected row (translate aL) (translate bR) =
      rowSelected row aL bR := by
  unfold rowSelected
  by_cases hb : bR ∈ zeroColumnSupport
  · have hs : translate bR ∈ zeroColumnSupport :=
      (translate_mem_column_iff bR).mpr hb
    rw [ite_eq_left hs, ite_eq_left hb, xor_translate_both]
  · have hs : translate bR ∉ zeroColumnSupport := by
      intro hh
      exact hb ((translate_mem_column_iff bR).mp hh)
    rw [ite_eq_right hs, ite_eq_right hb]

/-- Bookkeeping identity: excluded diagonal + selected = full mass. -/
theorem rowDefect_add_selected (row : Word → Nat) (aL bR : Word) :
    rowDefect row aL bR + rowSelected row aL bR = rowMass row aL := by
  classical
  by_cases hb : bR ∈ zeroColumnSupport
  · simp only [rowDefect, rowSelected, rowMass, ite_eq_left hb]
    exact Finset.sum_erase_add zeroColumnSupport
      (fun c => row (xor c aL)) hb
  · have he : zeroColumnSupport.erase bR = zeroColumnSupport :=
      Finset.erase_eq_of_notMem hb
    simp only [rowDefect, rowSelected, rowMass, he, ite_eq_right hb,
      Nat.add_zero]

/-- This is the symbolic version of the earlier 76-pair finite check:
    excluded-diagonal defect is invariant for ALL aL,bR and ANY row. -/
theorem rowDefect_translate (row : Word → Nat) (aL bR : Word) :
    rowDefect row (translate aL) (translate bR) =
      rowDefect row aL bR := by
  have hleft := rowDefect_add_selected row (translate aL) (translate bR)
  have hright := rowDefect_add_selected row aL bR
  rw [rowMass_translate, rowSelected_translate] at hleft
  omega

/-- The set of survivors is transported, not merely its cardinality. -/
def rowSurvivors (row : Word → Nat) (aL : Word) : Finset Word :=
  zeroColumnSupport.filter (fun c => 0 < row (xor c aL))

theorem rowSurvivors_translate (row : Word → Nat) (aL : Word) :
    rowSurvivors row (translate aL) = (rowSurvivors row aL).image translate := by
  ext c
  constructor
  · intro h
    obtain ⟨hc, hp⟩ := Finset.mem_filter.mp h
    apply Finset.mem_image.mpr
    refine ⟨translate c, ?_, translate_involutive c⟩
    apply Finset.mem_filter.mpr
    refine ⟨(translate_mem_column_iff c).mpr hc, ?_⟩
    rw [← xor_translate_right c aL]
    exact hp
  · intro h
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp h
    obtain ⟨hdcCol, hdpos⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    constructor
    · rw [← hdc]
      exact (translate_mem_column_iff d).mpr hdcCol
    · rw [← hdc, xor_translate_both]
      exact hdpos

theorem rowSurvivors_card_translate (row : Word → Nat) (aL : Word) :
    (rowSurvivors row (translate aL)).card = (rowSurvivors row aL).card := by
  rw [rowSurvivors_translate]
  exact Finset.card_image_of_injective _ translate_injective

/-! ## Instantiations for genuine Magma counts, ANY first-round key -/

/-- The *actual* surviving intermediate differences are equivariant
    under the column's shift even when k0 is even. -/
theorem survivingCandidates_translate (k₀ aL : Word) :
    survivingCandidates k₀ (translate aL) =
      (survivingCandidates k₀ aL).image translate := by
  exact rowSurvivors_translate (parityRowCount k₀) aL

theorem survivingCandidates_card_translate (k₀ aL : Word) :
    (survivingCandidates k₀ (translate aL)).card = (survivingCandidates k₀ aL).card := by
  exact rowSurvivors_card_translate (parityRowCount k₀) aL

/-- All eight-entry convolution terms together have the same actual mass. -/
theorem actual_convolution_translate (k₀ aL : Word) :
    (∑ c : Word, overlapWeight k₀ (0#32) (translate aL) (1#32) c) =
      ∑ c : Word, overlapWeight k₀ (0#32) aL (1#32) c := by
  rw [fullConvolution_eight_parity k₀ (translate aL),
    fullConvolution_eight_parity k₀ aL]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change 2 ^ 29 * rowMass (parityRowCount k₀) (translate aL) =
    2 ^ 29 * rowMass (parityRowCount k₀) aL
  rw [rowMass_translate]

/-- Simultaneously translating both differences preserves the selected
    three-round coefficient for every first and third key. -/
theorem actual_threeRound_translate (k₀ k₂ aL bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (translate aL, 1#32) (0#32, translate bR) =
      xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) := by
  rw [threeRound_zeroLeft_eight k₀ k₂ (translate aL) (translate bR),
    threeRound_zeroLeft_eight k₀ k₂ aL bR]
  by_cases hb : bR ∈ zeroColumnSupport
  · have hs : translate bR ∈ zeroColumnSupport :=
      (translate_mem_column_iff bR).mpr hb
    rw [ite_eq_left hs, ite_eq_left hb, xor_translate_both]
  · have hs : translate bR ∉ zeroColumnSupport := by
      intro hh
      exact hb ((translate_mem_column_iff bR).mp hh)
    rw [ite_eq_right hs, ite_eq_right hb]

/-- Stronger than the previously certified finite pair symmetry:
    ACTUAL defect invariance for all 2^64 pairs of 32-bit differences,
    for every first key (odd or even) and arbitrary third key. -/
theorem actual_couplingDefect_translate (k₀ k₂ aL bR : Word) :
    couplingDefect k₀ (0#32) k₂ (translate aL) (1#32)
        (0#32) (translate bR) =
      couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR := by
  rw [couplingDefect_eight_parity k₀ k₂ (translate aL) (translate bR),
    couplingDefect_eight_parity k₀ k₂ aL bR]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change 2 ^ 29 * rowDefect (parityRowCount k₀)
      (translate aL) (translate bR) =
    2 ^ 29 * rowDefect (parityRowCount k₀) aL bR
  rw [rowDefect_translate]

/-- A simultaneous XOR translation preserves the positivity predicates
    without assuming an odd key or using the 76-pair classification. -/
theorem actual_positive_and_defect_translate_iff (k₀ k₂ aL bR : Word) :
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (translate aL, 1#32) (0#32, translate bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ (translate aL) (1#32)
        (0#32) (translate bR)) ↔
    (0 < xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, bR) ∧
      0 < couplingDefect k₀ (0#32) k₂ aL (1#32) (0#32) bR) := by
  rw [actual_threeRound_translate, actual_couplingDefect_translate]

end Magma.DifanZeroKeyEightColumnSymmetry
