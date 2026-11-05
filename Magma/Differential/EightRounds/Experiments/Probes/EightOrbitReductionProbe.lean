module

import all Init.Data.Range.Basic
public import Difan.Symmetry.FiniteInvolutionOrbits
public import Magma.Differential.EightRounds.ZeroKeyEightGenericSymmetry
import Std.Tactic.BVDecide

@[expose] public section

/-!
# The 76 exact positive-defect pairs as 38 two-cycles

The shift by 0x00500000 on both difference coordinates preserves
both the certified 76-pair support and each exact reduced defect.
A strictly ordered rank of the LEFT input difference selects exactly
one representative of every orbit. The generic finite-involution
lemma then gives a twofold identity for arbitrary certified weights.
-/

namespace Magma.DifanZeroKeyEightOrbitReduction

open Magma
open Magma.MultiRoundDDT
open Magma.DifanThreeRoundCouplingDefect
open Magma.DifanZeroKeyEightDefectClassification
open Magma.DifanZeroKeyEightDefectWeights
open Magma.DifanZeroKeyEightDefectSpectrum
open Difan.FiniteInvolutionOrbits

private abbrev Word := V 32

/-- The first coordinate alone breaks the symmetry, so there is no
    need to order 64-bit pairs or invent a representation for them. -/
def leftRank (p : Word × Word) : Nat := p.1.toNat

/-- Every XOR orbit has two distinct left input differences. -/
theorem leftRank_ne_shift (p : Word × Word) :
    leftRank p ≠ leftRank (shiftPair p) := by
  change p.1.toNat ≠ (xor p.1 pairShiftMask).toNat
  intro heq
  have he : p.1 = xor p.1 pairShiftMask :=
    BitVec.eq_of_toNat_eq heq
  unfold xor pairShiftMask at he
  bv_decide

/-- The automatically chosen canonical orbit representatives. -/
def orbitRepresentatives : Finset (Word × Word) :=
  representatives positiveDefectPairs shiftPair leftRank

/-- The 76 selected pairs form exactly 38 two-element orbits. -/
theorem orbitRepresentatives_card : orbitRepresentatives.card = 38 := by
  have h := card_eq_twice_representatives
    positiveDefectPairs shiftPair leftRank
    shiftPair_involutive shiftedPairs_exact
    (fun p _ => leftRank_ne_shift p)
  change positiveDefectPairs.card = 2 * orbitRepresentatives.card at h
  rw [positiveDefectPairs_card] at h
  omega

set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- All 76 reduced defects are recovered by evaluating the 38
    canonical representatives once each. -/
theorem reduced_defect_orbit_sum :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) =
      2 * (∑ p ∈ orbitRepresentatives, reducedDefect p.1 p.2) := by
  exact sum_invariant positiveDefectPairs shiftPair leftRank
    shiftPair_involutive shiftedPairs_exact
    (fun p _ => leftRank_ne_shift p)
    (fun p => reducedDefect p.1 p.2)
    (fun p hp => shiftPair_preserves_defect p hp)

set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- The known total becomes a 38-term equality, certified by the
    symbolic orbit theorem rather than a second heavy DDT computation. -/
theorem reduced_defect_representatives_total :
    (∑ p ∈ orbitRepresentatives, reducedDefect p.1 p.2) =
      567541760 := by
  have h := reduced_defect_orbit_sum
  rw [defect_total_exact] at h
  omega


end Magma.DifanZeroKeyEightOrbitReduction
