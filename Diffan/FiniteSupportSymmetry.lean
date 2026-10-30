module

import all Init.Data.Range.Basic
public import Diffan.Composition

@[expose] public section

/-!
# Finite support symmetries and exact weighted sums

A finite support need not come from a cipher, nor does its weight function
have to be a DDT row.  A self-cancelling operation reduces the search for
translations preserving a nonempty support to pairwise differences of its
actual members.  Separately, an involution preserving the support transfers
weighted sums, selected terms, excluded-term defects, and positive support.

Concrete finite supports connect the candidate characterization with the
weighted invariance laws.
-/

namespace Diffan.FiniteSupportSymmetry

variable {W : Type*} [DecidableEq W]

/-- Candidate translations from pairs of members of the support. -/
def candidates (C : Finset W) (op : W → W → W) : Finset W :=
  (C.product C).image (fun p : W × W => op p.1 p.2)

/-- A finite computation of all support-preserving translations. -/
def stabilizers (C : Finset W) (op : W → W → W) : Finset W :=
  (candidates C op).filter
    (fun t => C.image (fun c => op c t) = C)

/-- Any stabilizer of a nonempty support is represented by a pair of
    members.  The only algebraic requirement is left self-cancellation. -/
theorem stabilizer_mem_candidates
    (C : Finset W) (op : W → W → W)
    (hcancel : ∀ x y, op x (op x y) = y)
    (hne : C.Nonempty) (t : W)
    (h : C.image (fun c => op c t) = C) :
    t ∈ candidates C op := by
  obtain ⟨c, hc⟩ := hne
  have hct : op c t ∈ C := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨(c, op c t), Finset.mem_product.mpr ⟨hc, hct⟩, ?_⟩
  exact hcancel c t

/-- The finite stabilizer computation is complete, even if W is huge.
    No law beyond self-cancellation, and no enumeration of W, is needed. -/
theorem stabilizer_iff_mem
    (C : Finset W) (op : W → W → W)
    (hcancel : ∀ x y, op x (op x y) = y)
    (hne : C.Nonempty) (t : W) :
    C.image (fun c => op c t) = C ↔ t ∈ stabilizers C op := by
  constructor
  · intro h
    exact Finset.mem_filter.mpr
      ⟨stabilizer_mem_candidates C op hcancel hne t h, h⟩
  · intro ht
    exact (Finset.mem_filter.mp ht).2

/-- Any involution preserving a finite support preserves membership. -/
theorem mem_involution_iff
    (C : Finset W) (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C) (c : W) :
    tr c ∈ C ↔ c ∈ C := by
  have forward (x : W) (hx : x ∈ C) : tr x ∈ C := by
    rw [← hstable]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  constructor
  · intro hc
    have hh := forward (tr c) hc
    simpa only [hinv] using hh
  · exact forward c

/-- Reindex a finite sum by a support-preserving involution. -/
theorem sum_involution
    (C : Finset W) (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C) (f : W → Nat) :
    (∑ c ∈ C, f (tr c)) = ∑ c ∈ C, f c := by
  have hinj : Set.InjOn tr (↑C) := by
    intro x _ y _ hxy
    have hh := congrArg tr hxy
    simpa only [hinv] using hh
  have hsum :
      (∑ c ∈ C.image tr, f c) = ∑ c ∈ C, f (tr c) :=
    Finset.sum_image hinj
  rw [← hsum, hstable]

/-! ## Arbitrary Nat-valued row weights -/

/-- The full weighted mass on a translated support. -/
def mass (C : Finset W) (op : W → W → W)
    (row : W → Nat) (a : W) : Nat :=
  ∑ c ∈ C, row (op c a)

/-- The selected term is zero outside the support. -/
def selected (C : Finset W) (op : W → W → W)
    (row : W → Nat) (a b : W) : Nat :=
  if b ∈ C then row (op b a) else 0

/-- The mass of all terms except the selected one. -/
def defect (C : Finset W) (op : W → W → W)
    (row : W → Nat) (a b : W) : Nat :=
  ∑ c ∈ C.erase b, row (op c a)

/-- Real positive-weight candidates, not a mere cardinality bound. -/
def survivors (C : Finset W) (op : W → W → W)
    (row : W → Nat) (a : W) : Finset W :=
  C.filter (fun c => 0 < row (op c a))

/-- The sum splits into its selected entry and its excluded-term defect. -/
theorem defect_add_selected
    (C : Finset W) (op : W → W → W)
    (row : W → Nat) (a b : W) :
    defect C op row a b + selected C op row a b =
      mass C op row a := by
  classical
  by_cases hb : b ∈ C
  · simp only [defect, selected, mass, ite_eq_left hb]
    exact Finset.sum_erase_add C (fun c => row (op c a)) hb
  · have he : C.erase b = C := Finset.erase_eq_of_notMem hb
    simp only [defect, selected, mass, he, ite_eq_right hb, Nat.add_zero]

/-- Moving the left parameter through a support symmetry leaves the full
    mass unchanged.  This needs no condition on the weight function. -/
theorem mass_invariant
    (C : Finset W) (op : W → W → W) (row : W → Nat)
    (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C)
    (hcross : ∀ c a, op c (tr a) = op (tr c) a)
    (a : W) :
    mass C op row (tr a) = mass C op row a := by
  unfold mass
  calc
    (∑ c ∈ C, row (op c (tr a))) =
        ∑ c ∈ C, row (op (tr c) a) := by
          apply Finset.sum_congr rfl
          intro c _
          exact congrArg row (hcross c a)
    _ = ∑ c ∈ C, row (op c a) :=
      sum_involution C tr hinv hstable (fun c => row (op c a))

/-- Simultaneously translating the left and selected indices leaves the
    selected coefficient unchanged. -/
theorem selected_invariant
    (C : Finset W) (op : W → W → W) (row : W → Nat)
    (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C)
    (hboth : ∀ c a, op (tr c) (tr a) = op c a)
    (a b : W) :
    selected C op row (tr a) (tr b) = selected C op row a b := by
  unfold selected
  by_cases hb : b ∈ C
  · have hs : tr b ∈ C :=
      (mem_involution_iff C tr hinv hstable b).mpr hb
    rw [ite_eq_left hs, ite_eq_left hb, hboth]
  · have hs : tr b ∉ C := by
      intro ht
      exact hb ((mem_involution_iff C tr hinv hstable b).mp ht)
    rw [ite_eq_right hs, ite_eq_right hb]

/-- The excluded-term defect inherits the same symmetry from the
    full-mass and selected-term laws. -/
theorem defect_invariant
    (C : Finset W) (op : W → W → W) (row : W → Nat)
    (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C)
    (hcross : ∀ c a, op c (tr a) = op (tr c) a)
    (hboth : ∀ c a, op (tr c) (tr a) = op c a)
    (a b : W) :
    defect C op row (tr a) (tr b) = defect C op row a b := by
  have hleft := defect_add_selected C op row (tr a) (tr b)
  have hright := defect_add_selected C op row a b
  rw [mass_invariant C op row tr hinv hstable hcross a,
    selected_invariant C op row tr hinv hstable hboth a b] at hleft
  omega

/-- Positive-weight survivors are transported as a SET, rather than
    only conserving their number. -/
theorem survivors_invariant
    (C : Finset W) (op : W → W → W) (row : W → Nat)
    (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C)
    (hcross : ∀ c a, op c (tr a) = op (tr c) a)
    (hboth : ∀ c a, op (tr c) (tr a) = op c a)
    (a : W) :
    survivors C op row (tr a) = (survivors C op row a).image tr := by
  ext c
  constructor
  · intro h
    obtain ⟨hc, hp⟩ := Finset.mem_filter.mp h
    apply Finset.mem_image.mpr
    refine ⟨tr c, ?_, hinv c⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_involution_iff C tr hinv hstable c).mpr hc, ?_⟩
    rw [← hcross c a]
    exact hp
  · intro h
    obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp h
    obtain ⟨hdcCol, hdpos⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    constructor
    · rw [← hdc]
      exact (mem_involution_iff C tr hinv hstable d).mpr hdcCol
    · rw [← hdc, hboth]
      exact hdpos

/-- Every positive multiplicity is invariant under translation. -/
theorem survivors_card_invariant
    (C : Finset W) (op : W → W → W) (row : W → Nat)
    (tr : W → W)
    (hinv : ∀ x, tr (tr x) = x)
    (hstable : C.image tr = C)
    (hcross : ∀ c a, op c (tr a) = op (tr c) a)
    (hboth : ∀ c a, op (tr c) (tr a) = op c a)
    (a : W) :
    (survivors C op row (tr a)).card =
      (survivors C op row a).card := by
  have hinj : Function.Injective tr := by
    intro x y hxy
    have hh := congrArg tr hxy
    simpa only [hinv] using hh
  rw [survivors_invariant C op row tr hinv hstable hcross hboth a]
  exact Finset.card_image_of_injective _ hinj

end Diffan.FiniteSupportSymmetry
