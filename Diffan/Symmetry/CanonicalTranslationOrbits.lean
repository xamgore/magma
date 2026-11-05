module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.FiniteTranslationOrbits

@[expose] public section

/-!
# Canonical representatives of finite translation orbits

Given a finite domain `C`, a finite collection `H` of translations and an
`act` operation, choose the least-ranked member of each orbit.  A rank need
only be injective WITHIN an orbit, not on the entire ambient space.

The assumptions below expose the real mathematical obligations:
* each point belongs to its own finite orbit;
* the orbit remains inside `C`;
* moving to a point of an orbit does not change that orbit;
* rank separates members of the same orbit;
* translation labels act freely on `C`.

From those properties the computed representatives are guaranteed to give
an `OrbitTiling`, and therefore the existing exact counting and weighted-sum
laws apply.
-/

namespace Diffan.CanonicalTranslationOrbits

variable {W T : Type*} [DecidableEq W]

/-- The finite orbit of a point under the provided translation labels. -/
def orbit (H : Finset T) (act : W → T → W) (x : W) : Finset W :=
  H.image (act x)

/-- One representative per orbit: the points with the least rank in
    their own orbit. No total order on `W` is required. -/
def canonicalRepresentatives (C : Finset W) (H : Finset T)
    (act : W → T → W) (rank : W → Nat) : Finset W :=
  C.filter (fun x => ∀ y ∈ orbit H act x, rank x ≤ rank y)

@[simp]
theorem mem_canonicalRepresentatives_iff (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat) (x : W) :
    x ∈ canonicalRepresentatives C H act rank ↔ x ∈ C ∧ ∀ y ∈ orbit H act x, rank x ≤ rank y := by
  simp [canonicalRepresentatives]

/-- Every point is in the translated orbit of a canonical representative.
    Existence is an ordinary minimum on a FINITE orbit. -/
theorem canonical_cover
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (hself : ∀ x ∈ C, x ∈ orbit H act x)
    (hstable : ∀ x ∈ C, ∀ y ∈ orbit H act x, y ∈ C)
    (horbit : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      orbit H act y = orbit H act x)
    (x : W) (hx : x ∈ C) :
    ∃ r ∈ canonicalRepresentatives C H act rank,
      ∃ t ∈ H, act r t = x := by
  classical
  obtain ⟨r, hrOrbit, hrLeast⟩ :=
    (orbit H act x).exists_min_image rank ⟨x, hself x hx⟩
  have hrC : r ∈ C := hstable x hx r hrOrbit
  have hrRep : r ∈ canonicalRepresentatives C H act rank := by
    apply (mem_canonicalRepresentatives_iff C H act rank r).mpr
    refine ⟨hrC, ?_⟩
    intro y hy
    apply hrLeast
    rw [← horbit x hx r hrOrbit]
    exact hy
  have hxOrbit : x ∈ orbit H act r := by
    rw [horbit x hx r hrOrbit]
    exact hself x hx
  obtain ⟨t, ht, htx⟩ := Finset.mem_image.mp hxOrbit
  exact ⟨r, hrRep, t, ht, htx⟩

/-- Distinct canonical representatives cannot describe the same point.
    Equality of ranks is used only INSIDE a single orbit. -/
theorem canonical_unique
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (hself : ∀ x ∈ C, x ∈ orbit H act x)
    (horbit : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      orbit H act y = orbit H act x)
    (hrank : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      rank x = rank y → x = y)
    (hfree : ∀ x ∈ C, ∀ t ∈ H, ∀ u ∈ H,
      act x t = act x u → t = u)
    (r s : W) (hr : r ∈ canonicalRepresentatives C H act rank)
    (hs : s ∈ canonicalRepresentatives C H act rank)
    (t u : T) (ht : t ∈ H) (hu : u ∈ H)
    (heq : act r t = act s u) :
    r = s ∧ t = u := by
  have hr' := (mem_canonicalRepresentatives_iff C H act rank r).mp hr
  have hs' := (mem_canonicalRepresentatives_iff C H act rank s).mp hs
  obtain ⟨hrC, hrMin⟩ := hr'
  obtain ⟨hsC, hsMin⟩ := hs'
  have hpR : act r t ∈ orbit H act r :=
    Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hpS : act r t ∈ orbit H act s := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hOrbits : orbit H act r = orbit H act s := calc
    orbit H act r = orbit H act (act r t) :=
      (horbit r hrC (act r t) hpR).symm
    _ = orbit H act s := horbit s hsC (act r t) hpS
  have hsInR : s ∈ orbit H act r := by
    rw [hOrbits]
    exact hself s hsC
  have hrInS : r ∈ orbit H act s := by
    rw [← hOrbits]
    exact hself r hrC
  have hRankEq : rank r = rank s :=
    Nat.le_antisymm (hrMin s hsInR) (hsMin r hrInS)
  have hrs : r = s := hrank r hrC s hsInR hRankEq
  constructor
  · exact hrs
  · subst s
    exact hfree r hrC t ht u hu heq

/-- The minimum-ranked representatives give an exact finite translation tiling. -/
theorem canonical_orbit_tiling
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (hself : ∀ x ∈ C, x ∈ orbit H act x)
    (hstable : ∀ x ∈ C, ∀ y ∈ orbit H act x, y ∈ C)
    (horbit : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      orbit H act y = orbit H act x)
    (hrank : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      rank x = rank y → x = y)
    (hfree : ∀ x ∈ C, ∀ t ∈ H, ∀ u ∈ H,
      act x t = act x u → t = u) :
    Diffan.FiniteTranslationOrbits.OrbitTiling C
      (canonicalRepresentatives C H act rank) H act := by
  apply Diffan.FiniteTranslationOrbits.orbitTiling_of_certificate
  · intro r hr t ht
    have hrC : r ∈ C :=
      ((mem_canonicalRepresentatives_iff C H act rank r).mp hr).1
    exact hstable r hrC (act r t)
      (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  · exact canonical_cover C H act rank hself hstable horbit
  · intro r hr s hs t ht u hu heq
    exact canonical_unique C H act rank hself horbit hrank hfree r s hr hs t u ht hu heq

/-- Cardinality follows for computed representatives, without a
    separately supplied list or a new finite certificate. -/
theorem canonical_card
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (hself : ∀ x ∈ C, x ∈ orbit H act x)
    (hstable : ∀ x ∈ C, ∀ y ∈ orbit H act x, y ∈ C)
    (horbit : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      orbit H act y = orbit H act x)
    (hrank : ∀ x ∈ C, ∀ y ∈ orbit H act x,
      rank x = rank y → x = y)
    (hfree : ∀ x ∈ C, ∀ t ∈ H, ∀ u ∈ H,
      act x t = act x u → t = u) :
    C.card = (canonicalRepresentatives C H act rank).card * H.card := by
  exact Diffan.FiniteTranslationOrbits.card_eq_representatives_mul_translations
    C (canonicalRepresentatives C H act rank) H act
    (canonical_orbit_tiling C H act rank hself hstable horbit hrank hfree)

/-- Exact weighted reduction (no invariance assumption). -/
theorem canonical_sum
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (htiling : Diffan.FiniteTranslationOrbits.OrbitTiling C
      (canonicalRepresentatives C H act rank) H act)
    (weight : W → Nat) :
    (∑ x ∈ C, weight x) =
      ∑ r ∈ canonicalRepresentatives C H act rank,
        ∑ t ∈ H, weight (act r t) := by
  exact Diffan.FiniteTranslationOrbits.sum_by_translations
    C (canonicalRepresentatives C H act rank) H act htiling weight

/-- Exact weighted reduction when all finite translations preserve weights. -/
theorem canonical_sum_invariant
    (C : Finset W) (H : Finset T) (act : W → T → W)
    (rank : W → Nat)
    (htiling : Diffan.FiniteTranslationOrbits.OrbitTiling C
      (canonicalRepresentatives C H act rank) H act)
    (weight : W → Nat)
    (hweight : ∀ r ∈ canonicalRepresentatives C H act rank,
      ∀ t ∈ H, weight (act r t) = weight r) :
    (∑ x ∈ C, weight x) =
      H.card * (∑ r ∈ canonicalRepresentatives C H act rank, weight r) := by
  exact Diffan.FiniteTranslationOrbits.sum_invariant
    C (canonicalRepresentatives C H act rank) H act htiling weight hweight

end Diffan.CanonicalTranslationOrbits
