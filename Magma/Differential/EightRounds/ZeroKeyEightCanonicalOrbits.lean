module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.CanonicalTranslationOrbits
public import Magma.Differential.EightRounds.ZeroKeyEightTranslationTiling

@[expose] public section

/-!
# Canonical generation of the 38 positive-defect pair orbits

The finite Bool translation action determines two-element orbits on the
76 positive-defect pairs. Selecting the member of each orbit with minimum
left-coordinate rank gives a canonical representative set and an exact
tiling through the generic orbit theorem.

The only nontrivial Magma inputs are the previously certified facts that
`shiftPair` preserves the 76-pair domain, has no fixed points, and preserves
reduced defect weights. The first difference coordinate ranks the two
members of every orbit strictly, even though this rank is not injective on
all 76 pairs.
-/

namespace Magma.DiffanZeroKeyEightCanonicalOrbits

open Magma
open Magma.DiffanZeroKeyEightDefectClassification
open Magma.DiffanZeroKeyEightDefectWeights
open Magma.DiffanZeroKeyEightDefectSpectrum
open Magma.DiffanZeroKeyEightOrbitReduction
open Magma.DiffanZeroKeyEightTranslationTiling
open Diffan.CanonicalTranslationOrbits
open Diffan.FiniteTranslationOrbits

private abbrev Word :=
  V 32

attribute [local irreducible] positiveDefectPairs

/-- Each Bool-translation orbit consists of a point and its XOR partner. -/
theorem bool_orbit_eq_pair (p : Word × Word) :
    orbit shifts shiftByBool p = {p, shiftPair p} := by
  classical
  ext q
  constructor
  · intro h
    change q ∈ shifts.image (shiftByBool p) at h
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
    cases b with
    | false =>
        change p = q at hb
        subst q
        simp
    | true =>
        change shiftPair p = q at hb
        subst q
        simp
  · intro h
    have hh : q = p ∨ q = shiftPair p := by simpa using h
    rcases hh with hq | hq
    · subst q
      exact Finset.mem_image.mpr
        ⟨false, Finset.mem_univ _, rfl⟩
    · subst q
      exact Finset.mem_image.mpr
        ⟨true, Finset.mem_univ _, rfl⟩

private theorem self_mem_orbit (p : Word × Word) (_ : p ∈ positiveDefectPairs) :
    p ∈ orbit shifts shiftByBool p := by
  rw [bool_orbit_eq_pair]
  simp

private theorem orbit_subset_pairs (p : Word × Word) (hp : p ∈ positiveDefectPairs)
    (q : Word × Word) (hq : q ∈ orbit shifts shiftByBool p) : q ∈ positiveDefectPairs := by
  rw [bool_orbit_eq_pair] at hq
  have h : q = p ∨ q = shiftPair p := by simpa using hq
  rcases h with h | h
  · simpa [h] using hp
  · simpa [h] using shiftPair_mem p hp

private theorem orbit_constant_on_orbit (p : Word × Word) (_ : p ∈ positiveDefectPairs)
    (q : Word × Word) (hq : q ∈ orbit shifts shiftByBool p) :
    orbit shifts shiftByBool q = orbit shifts shiftByBool p := by
  rw [bool_orbit_eq_pair] at hq
  have h : q = p ∨ q = shiftPair p := by simpa using hq
  rcases h with h | h
  · subst q
    rfl
  · subst q
    rw [bool_orbit_eq_pair, bool_orbit_eq_pair, shiftPair_involutive]
    ext x
    simp [or_comm]

private theorem left_rank_separates_orbit (p : Word × Word) (_ : p ∈ positiveDefectPairs)
    (q : Word × Word) (hq : q ∈ orbit shifts shiftByBool p) (heq : leftRank p = leftRank q) :
    p = q := by
  rw [bool_orbit_eq_pair] at hq
  have h : q = p ∨ q = shiftPair p := by simpa using hq
  rcases h with h | h
  · exact h.symm
  · rw [h] at heq
    exact False.elim ((leftRank_ne_shift p) heq)

private theorem bool_action_free (p : Word × Word) (_ : p ∈ positiveDefectPairs) (t : Bool)
    (ht : t ∈ shifts) (u : Bool) (hu : u ∈ shifts) (he : shiftByBool p t = shiftByBool p u) :
    t = u := by
  cases t <;> cases u
  · rfl
  · have hh : p = shiftPair p := he
    exact False.elim ((shiftPair_ne_self p) hh.symm)
  · have hh : shiftPair p = p := he
    exact False.elim ((shiftPair_ne_self p) hh)
  · rfl

/-- The minimum-ranked member of each orbit; ranks need only distinguish
    the two partners. -/
def canonicalPairs : Finset (Word × Word) :=
  canonicalRepresentatives positiveDefectPairs shifts shiftByBool leftRank

/-- Orbit closure, rank separation and freeness give an exact tiling
    by canonical representatives and the two Bool-labelled shifts. -/
theorem canonical_pairs_tiling :
    OrbitTiling positiveDefectPairs canonicalPairs shifts shiftByBool := by
  exact canonical_orbit_tiling positiveDefectPairs shifts shiftByBool leftRank
    self_mem_orbit orbit_subset_pairs orbit_constant_on_orbit
    left_rank_separates_orbit bool_action_free

/-- Canonically produced representatives give exactly 38 distinct orbits. -/
theorem canonical_pairs_card : canonicalPairs.card = 38 := by
  have h := card_eq_representatives_mul_translations
    positiveDefectPairs canonicalPairs shifts shiftByBool canonical_pairs_tiling
  have h76 : positiveDefectPairs.card = 76 := positiveDefectPairs_card
  have h2 : shifts.card = 2 := by decide
  rw [h76, h2] at h
  omega

/-- For two-element orbits with distinct ranks, the minimum-rank
    condition is equivalent to strict comparison with the partner rank. -/
theorem canonical_pairs_eq_prior : canonicalPairs = orbitRepresentatives := by
  ext p
  change (p ∈ canonicalRepresentatives positiveDefectPairs shifts
        shiftByBool leftRank) ↔
    p ∈ Diffan.FiniteInvolutionOrbits.representatives
      positiveDefectPairs shiftPair leftRank
  rw [mem_canonicalRepresentatives_iff,
      Diffan.FiniteInvolutionOrbits.mem_representatives_iff,
      bool_orbit_eq_pair]
  constructor
  · rintro ⟨hp, hmin⟩
    have hle : leftRank p ≤ leftRank (shiftPair p) := by
      apply hmin
      simp
    exact ⟨hp, lt_of_le_of_ne hle (leftRank_ne_shift p)⟩
  · rintro ⟨hp, hlt⟩
    refine ⟨hp, ?_⟩
    intro q hq
    have h : q = p ∨ q = shiftPair p := by simpa using hq
    rcases h with h | h
    · simp [h]
    · simpa [h] using Nat.le_of_lt hlt

/-- The sum of real normalized defects is automatically reduced to
    38 canonical values using the generic tiling law. -/
theorem reduced_defect_canonical_sum :
    (∑ p ∈ positiveDefectPairs, reducedDefect p.1 p.2) =
      shifts.card * (∑ p ∈ canonicalPairs, reducedDefect p.1 p.2) := by
  apply Diffan.CanonicalTranslationOrbits.canonical_sum_invariant
    positiveDefectPairs shifts shiftByBool leftRank canonical_pairs_tiling
    (fun p => reducedDefect p.1 p.2)
  intro p hp b hb
  have hpC : p ∈ positiveDefectPairs :=
    ((mem_canonicalRepresentatives_iff
      positiveDefectPairs shifts shiftByBool leftRank p).mp hp).1
  cases b with
  | false => rfl
  | true => simpa [shiftByBool] using shiftPair_preserves_defect p hpC

/-- The normalized defect total on the canonical representative set. -/
theorem canonical_reduced_defect_total :
    (∑ p ∈ canonicalPairs, reducedDefect p.1 p.2) = 567541760 := by
  rw [canonical_pairs_eq_prior]
  exact reduced_defect_representatives_total

end Magma.DiffanZeroKeyEightCanonicalOrbits
