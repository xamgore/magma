module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.FiniteSupportSymmetry

@[expose] public section

/-!
# Pair-orbit reduction on a finite invariant domain

An involution `flip` preserves a finite set `C`. A rank into Nat is used
only to choose one point from each orbit; no linear order on the original
type and no enumeration of its ambient universe are required.

The `rank_distinct` hypothesis excludes fixed points on C. Under this
hypothesis, `representatives` contains exactly one element per two-cycle.
Every Nat-valued weighted sum is then a sum of paired contributions. If
weights are invariant, the full sum is twice a representative sum.
-/

namespace Diffan.FiniteInvolutionOrbits

variable {W : Type*} [DecidableEq W]

/-- Rank-based canonical representative: take the element of each pair
    whose rank is strictly smaller than the rank of its partner. -/
def representatives (C : Finset W) (flip : W → W)
    (rank : W → Nat) : Finset W :=
  C.filter (fun x => rank x < rank (flip x))

omit [DecidableEq W] in
/-- Membership in the representative set exposes both the domain
    condition and the canonical-orientation inequality. -/
theorem mem_representatives_iff (C : Finset W) (flip : W → W)
    (rank : W → Nat) (x : W) :
    x ∈ representatives C flip rank ↔
      x ∈ C ∧ rank x < rank (flip x) := by
  simp [representatives]

/-- The opposite half is exactly the image of the representatives.
    `rank_distinct` is needed only on the finite domain C. -/
theorem complement_eq_image
    (C : Finset W) (flip : W → W) (rank : W → Nat)
    (hinv : ∀ x, flip (flip x) = x)
    (hstable : C.image flip = C)
    (rank_distinct : ∀ x ∈ C, rank x ≠ rank (flip x)) :
    C.filter (fun x => ¬ rank x < rank (flip x)) =
      (representatives C flip rank).image flip := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hn⟩ := Finset.mem_filter.mp hx
    have hlt : rank (flip x) < rank x :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (rank_distinct x hxC))
    apply Finset.mem_image.mpr
    refine ⟨flip x, ?_, hinv x⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact (Diffan.FiniteSupportSymmetry.mem_involution_iff
        C flip hinv hstable x).mpr hxC
    · simpa only [hinv] using hlt
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    obtain ⟨hyC, hlt⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    constructor
    · rw [← hxy]
      exact (Diffan.FiniteSupportSymmetry.mem_involution_iff
        C flip hinv hstable y).mpr hyC
    · rw [← hxy, hinv]
      exact not_lt.mpr (le_of_lt hlt)

/-- Pairwise grouping is exact even when the two members have
    DIFFERENT weights. -/
theorem sum_by_orbits
    (C : Finset W) (flip : W → W) (rank : W → Nat)
    (hinv : ∀ x, flip (flip x) = x)
    (hstable : C.image flip = C)
    (rank_distinct : ∀ x ∈ C, rank x ≠ rank (flip x))
    (weight : W → Nat) :
    (∑ x ∈ C, weight x) =
      ∑ x ∈ representatives C flip rank,
        (weight x + weight (flip x)) := by
  have hinj : Set.InjOn flip (↑(representatives C flip rank)) := by
    intro x _ y _ hxy
    have hh := congrArg flip hxy
    simpa only [hinv] using hh
  calc
    (∑ x ∈ C, weight x) =
        (∑ x ∈ representatives C flip rank, weight x) +
          (∑ x ∈ C.filter (fun x => ¬ rank x < rank (flip x)), weight x) := by
          simpa only [representatives] using
            (Finset.sum_filter_add_sum_filter_not C
              (fun x => rank x < rank (flip x)) weight).symm
    _ = (∑ x ∈ representatives C flip rank, weight x) +
          (∑ x ∈ representatives C flip rank, weight (flip x)) := by
          rw [complement_eq_image C flip rank hinv hstable rank_distinct]
          rw [Finset.sum_image hinj]
    _ = ∑ x ∈ representatives C flip rank,
          (weight x + weight (flip x)) := by
          rw [Finset.sum_add_distrib]

/-- When the weight is preserved by the involution, only one value
    per orbit needs to be evaluated. -/
theorem sum_invariant
    (C : Finset W) (flip : W → W) (rank : W → Nat)
    (hinv : ∀ x, flip (flip x) = x)
    (hstable : C.image flip = C)
    (rank_distinct : ∀ x ∈ C, rank x ≠ rank (flip x))
    (weight : W → Nat)
    (hweight : ∀ x ∈ C, weight (flip x) = weight x) :
    (∑ x ∈ C, weight x) =
      2 * (∑ x ∈ representatives C flip rank, weight x) := by
  calc
    _ = ∑ x ∈ representatives C flip rank,
          (weight x + weight (flip x)) :=
            sum_by_orbits C flip rank hinv hstable rank_distinct weight
    _ = ∑ x ∈ representatives C flip rank, 2 * weight x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxC : x ∈ C := (Finset.mem_filter.mp hx).1
          rw [hweight x hxC]
          omega
    _ = 2 * (∑ x ∈ representatives C flip rank, weight x) := by
          rw [Finset.mul_sum]

/-- The number of orbits is half the size of the invariant domain.
    There are no singleton orbits because rank distinguishes partners. -/
theorem card_eq_twice_representatives
    (C : Finset W) (flip : W → W) (rank : W → Nat)
    (hinv : ∀ x, flip (flip x) = x)
    (hstable : C.image flip = C)
    (rank_distinct : ∀ x ∈ C, rank x ≠ rank (flip x)) :
    C.card = 2 * (representatives C flip rank).card := by
  have hinj : Function.Injective flip := by
    intro x y hxy
    have hh := congrArg flip hxy
    simpa only [hinv] using hh
  have hparts := Finset.card_filter_add_card_filter_not (s := C)
    (fun x => rank x < rank (flip x))
  have hother :
      (C.filter (fun x => ¬ rank x < rank (flip x))).card =
        (representatives C flip rank).card := by
    rw [complement_eq_image C flip rank hinv hstable rank_distinct]
    exact Finset.card_image_of_injective _ hinj
  have hsum :
      (representatives C flip rank).card +
        (C.filter (fun x => ¬ rank x < rank (flip x))).card = C.card := by
    simpa only [representatives] using hparts
  rw [hother] at hsum
  omega

end Diffan.FiniteInvolutionOrbits
