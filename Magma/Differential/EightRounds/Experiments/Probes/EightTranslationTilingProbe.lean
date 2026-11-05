module

import all Init.Data.Range.Basic
public import Difan.Symmetry.FiniteTranslationOrbits
public import Magma.Differential.EightRounds.ZeroKeyEightOrbitReduction

@[expose] public section

/-!
# Certified finite translation tiling of the 76 positive-defect pairs

A Boolean label selects the neutral shift or the proved XOR shift.
`OrbitTiling` certifies that the 38 representatives and these two
translations parametrize the exact 76-pair support bijectively.

The weighted formulas instantiate the generic finite-translation theorem
with the reduced defect, which is constant on each two-element orbit.
-/

namespace Magma.DifanZeroKeyEightTranslationTiling

open Magma
open Magma.DifanZeroKeyEightDefectClassification
open Magma.DifanZeroKeyEightDefectWeights
open Magma.DifanZeroKeyEightDefectSpectrum
open Magma.DifanZeroKeyEightOrbitReduction
open Difan.FiniteTranslationOrbits

private abbrev Word := V 32

/-- Boolean identity/shift action, with no extra bit-vector assumptions. -/
def shiftByBool (p : Word × Word) (b : Bool) : Word × Word :=
  if b then shiftPair p else p

/-- The translation labels form a two-element finite set. -/
def shifts : Finset Bool := Finset.univ

/-- The rank-based representatives and two shifts cover each of the
    76 selected pairs exactly once. -/
theorem selected_pairs_tiling :
    OrbitTiling positiveDefectPairs orbitRepresentatives shifts
      shiftByBool := by
  decide +kernel

set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- The number of selected pairs is the product of the representative
    count and the number of translations. -/
theorem selected_pairs_card_via_tiling :
    positiveDefectPairs.card = orbitRepresentatives.card * shifts.card := by
  exact card_eq_representatives_mul_translations
    positiveDefectPairs orbitRepresentatives shifts shiftByBool
    selected_pairs_tiling

/-- The normalized defect is invariant under every allowed shift. -/
theorem reducedDefect_invariant_on_shifts
    (p : Word × Word) (hp : p ∈ orbitRepresentatives)
    (b : Bool) (hb : b ∈ shifts) :
    reducedDefect (shiftByBool p b).1 (shiftByBool p b).2 =
      reducedDefect p.1 p.2 := by
  have hpC : p ∈ positiveDefectPairs :=
    (Finset.mem_filter.mp hp).1
  cases b with
  | false => rfl
  | true =>
      simpa [shiftByBool] using shiftPair_preserves_defect p hpC

set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- One generic orbit sum replaces all 76 evaluations by 38
    independent representative weights. -/
theorem reduced_defect_sum_via_tiling :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) =
      shifts.card *
        (∑ p ∈ orbitRepresentatives, reducedDefect p.1 p.2) := by
  apply sum_invariant positiveDefectPairs orbitRepresentatives shifts
    shiftByBool selected_pairs_tiling (fun p => reducedDefect p.1 p.2)
  intro p hp b hb
  exact reducedDefect_invariant_on_shifts p hp b hb

/-- This recovers the previously certified numerical identity by
    substitution of the two-shift cardinality. -/
theorem reduced_defect_total_via_tiling :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) =
      2 * 567541760 := by
  rw [reduced_defect_sum_via_tiling, reduced_defect_representatives_total]
  decide

end Magma.DifanZeroKeyEightTranslationTiling
