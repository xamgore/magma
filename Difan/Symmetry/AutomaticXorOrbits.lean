module

import all Init.Data.Range.Basic
public import Difan.Symmetry.CanonicalTranslationOrbits
public import Difan.Symmetry.FiniteSupportSymmetry

@[expose] public section

/-!
# Automatically certified XOR-translation orbits of finite BitVec supports

For a nonempty finite `C : Finset (BitVec n)`, its XOR-translation
stabilizer can be found among differences of pairs of support points.

XOR cancellation makes the action free on words: `x ^^^ t = x ^^^ u`
implies `t = u`. Projections or observations of words need not retain
this property.

Choosing the least natural-valued member of each orbit gives an exact
tiling, a cardinality identity, and a weighted-sum identity.
-/

namespace Difan.AutomaticXorOrbits

open Difan.CanonicalTranslationOrbits
open Difan.FiniteTranslationOrbits
open Difan.FiniteSupportSymmetry
variable {n : Nat}

/-- XOR differences of entries, filtered for support preservation. -/
def shifts (C : Finset (BitVec n)) : Finset (BitVec n) :=
  stabilizers C (fun x t => x ^^^ t)

/-- Exactly one least (natural-value) member from every XOR orbit. -/
def representatives (C : Finset (BitVec n)) : Finset (BitVec n) :=
  canonicalRepresentatives C (shifts C)
    (fun x t => x ^^^ t) BitVec.toNat

private theorem xor_cancel (x y : BitVec n) : x ^^^ (x ^^^ y) = y := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- This finite search is complete on every nonempty finite support. -/
theorem mem_shifts_iff (C : Finset (BitVec n)) (hne : C.Nonempty)
    (t : BitVec n) :
    t ∈ shifts C ↔ C.image (fun x => x ^^^ t) = C := by
  exact (stabilizer_iff_mem C (fun x t => x ^^^ t)
    xor_cancel hne t).symm

/-- The identity shift belongs to the automatically discovered family. -/
theorem zero_mem_shifts (C : Finset (BitVec n)) (hne : C.Nonempty) :
    (0#n) ∈ shifts C := by
  exact zero_mem_stabilizers C (fun x t => x ^^^ t) (0#n)
    xor_cancel (fun _ => BitVec.xor_zero) hne

/-- Computed support-preserving shifts are closed under XOR. -/
theorem shifts_xor_closed (C : Finset (BitVec n)) (hne : C.Nonempty)
    (t u : BitVec n) (ht : t ∈ shifts C) (hu : u ∈ shifts C) :
    (t ^^^ u) ∈ shifts C := by
  exact stabilizers_closed C (fun x t => x ^^^ t)
    xor_cancel (fun x y z => BitVec.xor_assoc x y z)
    hne t u ht hu

/-- XOR cancellation makes the action free on every support. -/
theorem xor_action_free (x t u : BitVec n)
    (heq : x ^^^ t = x ^^^ u) : t = u := by
  exact (BitVec.xor_right_inj x).mp heq

/-- The orbit of a point contains that point. -/
private theorem self_mem_orbit (C : Finset (BitVec n)) (hne : C.Nonempty)
    (x : BitVec n) (_ : x ∈ C) :
    x ∈ orbit (shifts C) (fun x t => x ^^^ t) x := by
  change x ∈ (shifts C).image (fun t => x ^^^ t)
  exact Finset.mem_image.mpr
    ⟨0#n, zero_mem_shifts C hne, by simp⟩

/-- Translating a support member by any found shift stays in the support. -/
private theorem orbit_stable (C : Finset (BitVec n)) (hne : C.Nonempty)
    (x : BitVec n) (hx : x ∈ C)
    (y : BitVec n) (hy : y ∈ orbit (shifts C) (fun x t => x ^^^ t) x) :
    y ∈ C := by
  change y ∈ (shifts C).image (fun t => x ^^^ t) at hy
  obtain ⟨t, ht, hty⟩ := Finset.mem_image.mp hy
  have hC : C.image (fun z => z ^^^ t) = C :=
    (mem_shifts_iff C hne t).mp ht
  rw [← hty, ← hC]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Shifting a point inside its orbit does not change the orbit.
    This uses closure of computed masks under XOR. -/
private theorem orbit_constant (C : Finset (BitVec n)) (hne : C.Nonempty)
    (x : BitVec n) (_ : x ∈ C)
    (y : BitVec n) (hy : y ∈ orbit (shifts C) (fun x t => x ^^^ t) x) :
    orbit (shifts C) (fun x t => x ^^^ t) y =
      orbit (shifts C) (fun x t => x ^^^ t) x := by
  change y ∈ (shifts C).image (fun t => x ^^^ t) at hy
  obtain ⟨t, ht, hty⟩ := Finset.mem_image.mp hy
  ext z
  constructor
  · intro hz
    change z ∈ (shifts C).image (fun u => y ^^^ u) at hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
    change z ∈ (shifts C).image (fun v => x ^^^ v)
    refine Finset.mem_image.mpr
      ⟨t ^^^ u, shifts_xor_closed C hne t u ht hu, ?_⟩
    calc
      x ^^^ (t ^^^ u) = (x ^^^ t) ^^^ u := (BitVec.xor_assoc x t u).symm
      _ = y ^^^ u := by rw [hty]
      _ = z := huz
  · intro hz
    change z ∈ (shifts C).image (fun u => x ^^^ u) at hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
    change z ∈ (shifts C).image (fun v => y ^^^ v)
    refine Finset.mem_image.mpr
      ⟨t ^^^ u, shifts_xor_closed C hne t u ht hu, ?_⟩
    calc
      y ^^^ (t ^^^ u) = (x ^^^ t) ^^^ (t ^^^ u) := by rw [hty]
      _ = x ^^^ (t ^^^ (t ^^^ u)) := BitVec.xor_assoc x t (t ^^^ u)
      _ = x ^^^ u := by rw [xor_cancel]
      _ = z := huz

/-- Automatically generated stabilizers and representatives form an exact
    orbit tiling.  The freeness obligation is solved by XOR cancellation. -/
theorem automatic_tiling (C : Finset (BitVec n)) (hne : C.Nonempty) :
    OrbitTiling C (representatives C) (shifts C)
      (fun x t => x ^^^ t) := by
  unfold representatives
  apply canonical_orbit_tiling C (shifts C)
    (fun x t => x ^^^ t) BitVec.toNat
  · exact self_mem_orbit C hne
  · exact orbit_stable C hne
  · exact orbit_constant C hne
  · intro x hx y hy heq
    exact BitVec.toNat_injective heq
  · intro x hx t ht u hu heq
    exact xor_action_free x t u heq

/-- Every orbit has `|H|` points: no Burnside correction term occurs. -/
theorem card_eq (C : Finset (BitVec n)) (hne : C.Nonempty) :
    C.card = (representatives C).card * (shifts C).card := by
  exact card_eq_representatives_mul_translations C
    (representatives C) (shifts C) (fun x t => x ^^^ t)
    (automatic_tiling C hne)

/-- Sum an arbitrary weight over the translates of canonical representatives. -/
theorem sum_eq (C : Finset (BitVec n)) (hne : C.Nonempty)
    (weight : BitVec n → Nat) :
    (∑ x ∈ C, weight x) =
      ∑ r ∈ representatives C, ∑ t ∈ shifts C, weight (r ^^^ t) := by
  exact sum_by_translations C (representatives C) (shifts C)
    (fun x t => x ^^^ t) (automatic_tiling C hne) weight

/-- Only with a proved weight invariance may we multiply by |H|. -/
theorem invariant_sum_eq (C : Finset (BitVec n)) (hne : C.Nonempty)
    (weight : BitVec n → Nat)
    (hinvariant : ∀ x ∈ C, ∀ t ∈ shifts C, weight (x ^^^ t) = weight x) :
    (∑ x ∈ C, weight x) =
      (shifts C).card * (∑ r ∈ representatives C, weight r) := by
  apply sum_invariant C (representatives C) (shifts C)
    (fun x t => x ^^^ t) (automatic_tiling C hne) weight
  intro r hr t ht
  exact hinvariant r ((Difan.CanonicalTranslationOrbits.mem_canonicalRepresentatives_iff
    C (shifts C) (fun x t => x ^^^ t) BitVec.toNat r).mp hr).1 t ht

end Difan.AutomaticXorOrbits
