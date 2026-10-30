module

import all Init.Data.Range.Basic
public import Diffan.FiniteInvolutionOrbits
public import Magma.Diffan.ZeroKeyEightGenericSymmetry
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

namespace Magma.DiffanZeroKeyEightOrbitReduction

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanZeroKeyEightDefectClassification
open Magma.DiffanZeroKeyEightDefectWeights
open Magma.DiffanZeroKeyEightDefectSpectrum
open Diffan.FiniteInvolutionOrbits

private abbrev Word :=
  V 32

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

attribute [local irreducible] positiveDefectPairs

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

/-- The known total becomes a 38-term equality, certified by the
    symbolic orbit theorem rather than a second heavy DDT computation. -/
theorem reduced_defect_representatives_total :
    (∑ p ∈ orbitRepresentatives, reducedDefect p.1 p.2) =
      567541760 := by
  have h := reduced_defect_orbit_sum
  rw [defect_total_exact] at h
  omega

/-- The actual, unnormalized three-round defect admits the same
    representative reduction for every odd first-round key. -/
theorem odd_actual_defect_orbit_sum
    (k₀ k₂ : Word) (hk : k₀.toNat % 2 = 1) :
    (∑ p ∈ positiveDefectPairs,
      couplingDefect k₀ (0#32) k₂ p.1 (1#32) (0#32) p.2) =
      2 * (∑ p ∈ orbitRepresentatives,
        couplingDefect k₀ (0#32) k₂ p.1 (1#32) (0#32) p.2) := by
  apply sum_invariant positiveDefectPairs shiftPair leftRank
    shiftPair_involutive shiftedPairs_exact
    (fun p _ => leftRank_ne_shift p)
  intro p hp
  simpa only [shiftPair] using
    odd_actual_defect_shift k₀ k₂ p.1 p.2 hk hp

/-- As a consequence, the actual total on the 38 representatives
    is uniform in the first odd round key and the arbitrary third key. -/
theorem odd_actual_defect_representatives_total
    (k₀ k₂ : Word) (hk : k₀.toNat % 2 = 1) :
    (∑ p ∈ orbitRepresentatives,
      couplingDefect k₀ (0#32) k₂ p.1 (1#32) (0#32) p.2) =
        2 ^ 29 * 567541760 := by
  have h := odd_actual_defect_orbit_sum k₀ k₂ hk
  rw [odd_actual_defect_total k₀ k₂ hk] at h
  norm_num at h ⊢
  omega

end Magma.DiffanZeroKeyEightOrbitReduction
