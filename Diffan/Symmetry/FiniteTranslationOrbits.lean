module

import all Init.Data.Range.Basic
public import Diffan.Symmetry.FiniteInvolutionOrbits

@[expose] public section

/-!
# Finite translation orbit certificates

`OrbitTiling` says that a finite collection `R` of representatives and a
finite collection `H` of translations parametrize a finite domain `C`
exactly once.  It is a predicate, not a data-bearing cipher abstraction.

The true content is a bijection of finite sets.  The associated cardinality,
weighted-sum, and invariant-weight formulas transport counts through this
bijection. The labels of translations
can have a different type from the states being translated.

For XOR supports, the second part proves that support-preserving shifts
are closed under XOR.  By `FiniteSupportSymmetry.stabilizer_iff_mem`, the
complete stabilizer can be discovered by checking only pairwise differences
of elements of a nonempty support.  Thus a small finite table may certify a
whole translation group without enumerating the ambient word type.
-/

namespace Diffan.FiniteTranslationOrbits

variable {W T : Type*} [DecidableEq W]

/-- A finite exact tiling: every point of C has a unique (representative,
    translation) description.  This can be checked on finite tables or
    established symbolically. -/
def OrbitTiling (C R : Finset W) (H : Finset T)
    (act : W → T → W) : Prop :=
  (R.product H).image (fun p => act p.1 p.2) = C ∧
  Set.InjOn (fun p : W × T => act p.1 p.2) (↑(R.product H))

/-- Supply soundness, coverage and uniqueness rather than building an
    `Equiv` by hand.  These three obligations are the certificate. -/
theorem orbitTiling_of_certificate
    (C R : Finset W) (H : Finset T) (act : W → T → W)
    (hsound : ∀ r ∈ R, ∀ t ∈ H, act r t ∈ C)
    (hcover : ∀ x ∈ C, ∃ r ∈ R, ∃ t ∈ H, act r t = x)
    (hunique : ∀ r ∈ R, ∀ s ∈ R, ∀ t ∈ H, ∀ u ∈ H,
      act r t = act s u → r = s ∧ t = u) :
    OrbitTiling C R H act := by
  classical
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨⟨r, t⟩, hrt, heq⟩ := Finset.mem_image.mp hx
      obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrt
      rw [← heq]
      exact hsound r hr t ht
    · intro hx
      obtain ⟨r, hr, t, ht, heq⟩ := hcover x hx
      exact Finset.mem_image.mpr
        ⟨(r, t), Finset.mem_product.mpr ⟨hr, ht⟩, heq⟩
  · intro p hp q hq heq
    rcases p with ⟨r, t⟩
    rcases q with ⟨s, u⟩
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hp
    obtain ⟨hs, hu⟩ := Finset.mem_product.mp hq
    obtain ⟨hrs, htu⟩ := hunique r hr s hs t ht u hu heq
    exact Prod.ext hrs htu

/-- The finite-domain cardinality is the number of orbits times the
    number of translations, provided the tiling is certified. -/
theorem card_eq_representatives_mul_translations
    (C R : Finset W) (H : Finset T) (act : W → T → W)
    (htiling : OrbitTiling C R H act) :
    C.card = R.card * H.card := by
  classical
  obtain ⟨himage, hinj⟩ := htiling
  calc
    C.card = ((R.product H).image
        (fun p : W × T => act p.1 p.2)).card :=
          congrArg Finset.card himage.symm
    _ = (R.product H).card := Finset.card_image_of_injOn hinj
    _ = R.card * H.card := Finset.card_product R H

/-- An exact sum over arbitrary weights, without requiring invariance.
    We may evaluate by orbits but still retain all distinct weights. -/
theorem sum_by_translations
    (C R : Finset W) (H : Finset T) (act : W → T → W)
    (htiling : OrbitTiling C R H act) (weight : W → Nat) :
    (∑ x ∈ C, weight x) =
      ∑ r ∈ R, ∑ t ∈ H, weight (act r t) := by
  classical
  obtain ⟨himage, hinj⟩ := htiling
  calc
    (∑ x ∈ C, weight x) =
        ∑ x ∈ (R.product H).image
          (fun p : W × T => act p.1 p.2), weight x := by rw [himage]
    _ = ∑ p ∈ R.product H, weight (act p.1 p.2) :=
          Finset.sum_image hinj
    _ = ∑ r ∈ R, ∑ t ∈ H, weight (act r t) := by
          exact Finset.sum_product R H (fun p => weight (act p.1 p.2))

/-- If each translation preserves a weight, the entire finite sum is
    reduced to one evaluation per representative. -/
theorem sum_invariant
    (C R : Finset W) (H : Finset T) (act : W → T → W)
    (htiling : OrbitTiling C R H act) (weight : W → Nat)
    (hweight : ∀ r ∈ R, ∀ t ∈ H, weight (act r t) = weight r) :
    (∑ x ∈ C, weight x) =
      H.card * (∑ r ∈ R, weight r) := by
  calc
    _ = ∑ r ∈ R, ∑ t ∈ H, weight (act r t) :=
      sum_by_translations C R H act htiling weight
    _ = ∑ r ∈ R, H.card * weight r := by
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ t ∈ H, weight (act r t)) =
            ∑ t ∈ H, weight r := by
              apply Finset.sum_congr rfl
              intro t ht
              exact hweight r hr t ht
        _ = H.card * weight r := by simp
    _ = H.card * (∑ r ∈ R, weight r) := by
      rw [Finset.mul_sum]

end Diffan.FiniteTranslationOrbits

namespace Diffan.FiniteTranslationOrbits

variable {W : Type*} [DecidableEq W]

/-- Composing two support-preserving XOR translations preserves the
    same support.  No finite enumeration or DDT fact is needed. -/
theorem translation_stable_comp
    (C : Finset W) (op : W → W → W)
    (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (t u : W)
    (ht : C.image (fun x => op x t) = C)
    (hu : C.image (fun x => op x u) = C) :
    C.image (fun x => op x (op t u)) = C := by
  calc
    C.image (fun x => op x (op t u)) =
        C.image ((fun x => op x u) ∘ (fun x => op x t)) := by
          congr 1
          funext x
          exact (hassoc x t u).symm
    _ = (C.image (fun x => op x t)).image (fun x => op x u) := by
          rw [Finset.image_image]
    _ = C := by rw [ht, hu]

/-- The finite candidate-set computation is closed under combining
    two certified XOR shifts.  Self-cancellation is only needed to
    show candidate-search completeness. -/
theorem stabilizers_closed
    (C : Finset W) (op : W → W → W)
    (hcancel : ∀ x y, op x (op x y) = y)
    (hassoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hne : C.Nonempty) (t u : W)
    (ht : t ∈ Diffan.FiniteSupportSymmetry.stabilizers C op)
    (hu : u ∈ Diffan.FiniteSupportSymmetry.stabilizers C op) :
    op t u ∈ Diffan.FiniteSupportSymmetry.stabilizers C op := by
  have ht' := (Diffan.FiniteSupportSymmetry.stabilizer_iff_mem
    C op hcancel hne t).mpr ht
  have hu' := (Diffan.FiniteSupportSymmetry.stabilizer_iff_mem
    C op hcancel hne u).mpr hu
  exact (Diffan.FiniteSupportSymmetry.stabilizer_iff_mem
    C op hcancel hne (op t u)).mp
    (translation_stable_comp C op hassoc t u ht' hu')

/-- The neutral XOR shift is always in the computed stabilizer
    of a nonempty finite support. -/
theorem zero_mem_stabilizers
    (C : Finset W) (op : W → W → W) (zero : W)
    (hcancel : ∀ x y, op x (op x y) = y)
    (hzero : ∀ x, op x zero = x)
    (hne : C.Nonempty) :
    zero ∈ Diffan.FiniteSupportSymmetry.stabilizers C op := by
  apply (Diffan.FiniteSupportSymmetry.stabilizer_iff_mem
    C op hcancel hne zero).mp
  have hid : (fun x : W => op x zero) = id :=
    funext (fun x => hzero x)
  simp only [hid, Finset.image_id]

end Diffan.FiniteTranslationOrbits
