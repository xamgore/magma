module

import all Init.Data.Range.Basic
public import Magma.Differential.EightRounds.ZeroKeyEightSharpBound
import Std.Tactic.BVDecide

@[expose] public section

/-!
# Multiplicity of the zero-second-key eight-column overlap

The only possible nonempty left differences are XORs
of an element in the certified 77-entry odd unit row and an element in
the certified eight-entry zero-key column (at most 77 * 8 pairs).

For every odd first-round key the multiplicity distribution is:

  cardinality 1 : 540 left input differences
  cardinality 2 :   6
  cardinality 3 :  12
  cardinality 4 :   4
  cardinality 5 :   0
  cardinality 6 :   2

The 24 differences of multiplicity at least two are tabulated explicitly.
They occupy only two 28-bit projection classes. The remaining 2^32 - 564
left differences have empty intersection.
-/

namespace Magma.DifanZeroKeyEightMultiplicity

open Magma
open Magma.OddUnitInput77
open Magma.DifanZeroKeyEightColumn
open Magma.DifanZeroKeyEightSharpBound
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word := V 32

/-- Reuse only the positive support of the 77-entry odd row. -/
def oddSurvivors (aL : Word) : Finset Word :=
  zeroColumnSupport.filter (fun c => xor c aL ∈ oddOutputSupport)

/-- For arbitrary ODD k0, the exact survivors depend only on aL. -/
theorem odd_survivors_eq (k₀ aL : Word) (hk : k₀.toNat % 2 = 1) :
    survivingCandidates k₀ aL = oddSurvivors aL := by
  ext c
  rw [odd_surviving_iff k₀ aL c hk]
  simp only [oddSurvivors, Finset.mem_filter]

/-- The *finite* candidate domain, generated from 77 * 8 pairs.
    Duplicates are automatically removed by `Finset.image`. -/
def oddCandidateInputs : Finset Word :=
  (oddOutputSupport.product zeroColumnSupport).image
    (fun dc : Word × Word => xor dc.1 dc.2)

set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- A left difference has any survivors iff it belongs to the finite
    domain of XOR pairs. The proof is symbolic in aL, not a full-word scan. -/
theorem candidate_iff_nonempty (aL : Word) :
    aL ∈ oddCandidateInputs ↔ (oddSurvivors aL).Nonempty := by
  constructor
  · intro ha
    obtain ⟨⟨d, c⟩, hdc, heq⟩ := Finset.mem_image.mp ha
    obtain ⟨hd, hc⟩ := Finset.mem_product.mp hdc
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩⟩
    have h : xor c aL = d := by
      change xor d c = aL at heq
      rw [← heq]
      unfold xor
      bv_decide
    rw [h]
    exact hd
  · rintro ⟨c, hc⟩
    obtain ⟨hcol, hrow⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_image.mpr
    refine ⟨(xor c aL, c), Finset.mem_product.mpr ⟨hrow, hcol⟩, ?_⟩
    change xor (xor c aL) c = aL
    unfold xor
    bv_decide


end Magma.DifanZeroKeyEightMultiplicity
