module

import all Init.Data.Range.Basic
public import Diffan.AutomaticXorOrbits
public import Magma.Composition.ZeroLeft.ParityCompleteSlice
import Std.Tactic.BVDecide

@[expose] public section

/-!
# XOR symmetries of both exact unit-input DDT rows of Magma

For the real g[k] with input XOR difference 1, the support is the
certified eight-offset row for even keys and the certified 77-offset
row for odd keys.  The automatic stabilizer search gives two masks in
the even case, but only the zero mask in the odd case.

The odd certificate uses one anchor and two support probes to eliminate
every nonzero candidate shift. Its translation orbits are singletons.
-/

namespace Magma.DiffanUnitInputAutomaticSymmetryAudit

open Magma
open Magma.CarryAutomaton
open Magma.ZeroLeftEightEntries
open Magma.OddUnitInput77
open Magma.ZeroLeftParityCompleteSlice

private abbrev Word :=
  V 32

private theorem even_nonempty : eightOffsets.Nonempty :=
  ⟨0x00001000#32, by decide⟩

/-- The even-key row has exactly one nonzero translation symmetry. -/
theorem even_shifts_exact :
    Diffan.AutomaticXorOrbits.shifts eightOffsets =
      ({0#32, 0x00006000#32} : Finset Word) := by
  decide +kernel

/-- For arbitrary even round keys, both the support and the exact DDT
    coefficients are invariant under XOR 0x6000. -/
theorem even_key_DDT_translation (k d : Word)
    (hk : k.toNat % 2 = 0) :
    xorDDT_g k (1#32) (d ^^^ 0x00006000#32) =
      xorDDT_g k (1#32) d := by
  have ht : (0x00006000#32 : Word) ∈
      Diffan.AutomaticXorOrbits.shifts eightOffsets := by
    rw [even_shifts_exact]
    decide
  have hstable : eightOffsets.image (fun x => x ^^^ (0x00006000#32)) =
      eightOffsets :=
    (Diffan.AutomaticXorOrbits.mem_shifts_iff
      eightOffsets even_nonempty (0x00006000#32)).mp ht
  have hmem (x : Word) :
      x ^^^ (0x00006000#32) ∈ eightOffsets ↔ x ∈ eightOffsets := by
    have hforward (y : Word) (hy : y ∈ eightOffsets) :
        y ^^^ (0x00006000#32) ∈ eightOffsets := by
      rw [← hstable]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    constructor
    · intro hx
      have hh := hforward (x ^^^ (0x00006000#32)) hx
      have hcancel :
          (x ^^^ (0x00006000#32)) ^^^ (0x00006000#32) = x := by
        bv_decide
      simpa only [hcancel] using hh
    · exact hforward x
  rw [Magma.UnitInputParityReduction.unitInput_DDT_even_key
        k (d ^^^ (0x00006000#32)) hk,
      Magma.UnitInputParityReduction.unitInput_DDT_even_key k d hk]
  rw [zeroKey_first_row_exact, zeroKey_first_row_exact]
  simp only [hmem]

/-! ## A bounded non-symmetry certificate for the 77-word odd row -/

private theorem odd_probes_mem :
    (0x00001000#32 : Word) ∈ oddOutputSupport ∧
      (0x00002800#32 : Word) ∈ oddOutputSupport ∧ (0x00003800#32 : Word) ∈ oddOutputSupport := by
  decide +kernel

private theorem odd_nonempty : oddOutputSupport.Nonempty :=
  ⟨0x00001000#32, odd_probes_mem.1⟩

/-- A preserving shift t must satisfy anchor XOR t ∈ support.
    Consequently it is among 77 anchored candidates, not 2^32. -/
private def oddAnchorCandidates : Finset Word :=
  oddOutputSupport.image (fun x => (0x00001000#32) ^^^ x)

/-- The first probe cuts the 77 candidates down to two masks. -/
private def oddFirstProbe : Finset Word :=
  oddAnchorCandidates.filter
    (fun t => (0x00002800#32) ^^^ t ∈ oddOutputSupport)

private theorem odd_first_probe_exact : oddFirstProbe = ({0#32, 0x00003800#32} : Finset Word) := by
  decide +kernel

/-- The second probe eliminates the last nonzero candidate. -/
private def oddSecondProbe : Finset Word :=
  oddFirstProbe.filter
    (fun t => (0x00003800#32) ^^^ t ∈ oddOutputSupport)

private theorem odd_second_probe_exact : oddSecondProbe = ({0#32} : Finset Word) := by
  unfold oddSecondProbe
  rw [odd_first_probe_exact]
  decide +kernel

attribute [local irreducible] Diffan.AutomaticXorOrbits.shifts

private theorem mem_support_after_shift (C : Finset Word) (hne : C.Nonempty) (t x : Word)
    (ht : t ∈ Diffan.AutomaticXorOrbits.shifts C) (hx : x ∈ C) : x ^^^ t ∈ C := by
  have hstable := (Diffan.AutomaticXorOrbits.mem_shifts_iff C hne t).mp ht
  rw [← hstable]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The odd-key support has no nonzero translation symmetry: the two probes
    eliminate every nonzero anchored candidate. -/
theorem odd_shifts_exact :
    Diffan.AutomaticXorOrbits.shifts oddOutputSupport =
      ({0#32} : Finset Word) := by
  ext t
  constructor
  · intro ht
    have ha := mem_support_after_shift oddOutputSupport odd_nonempty
      t (0x00001000#32) ht odd_probes_mem.1
    have hp := mem_support_after_shift oddOutputSupport odd_nonempty
      t (0x00002800#32) ht odd_probes_mem.2.1
    have hq := mem_support_after_shift oddOutputSupport odd_nonempty
      t (0x00003800#32) ht odd_probes_mem.2.2
    have hc : t ∈ oddAnchorCandidates := by
      unfold oddAnchorCandidates
      apply Finset.mem_image.mpr
      refine ⟨(0x00001000#32) ^^^ t, ha, ?_⟩
      bv_decide
    have h1 : t ∈ oddFirstProbe :=
      Finset.mem_filter.mpr ⟨hc, hp⟩
    have h2 : t ∈ oddSecondProbe :=
      Finset.mem_filter.mpr ⟨h1, hq⟩
    rw [odd_second_probe_exact] at h2
    exact h2
  · intro ht
    have hz : t = (0#32) := Finset.mem_singleton.mp ht
    subst t
    exact Diffan.AutomaticXorOrbits.zero_mem_shifts
      oddOutputSupport odd_nonempty

/-- The full XOR-translation group of the exact reference row is
    determined solely by the parity of the actual 32-bit round key. -/
theorem all_keys_shifts_exact (k : Word) :
    Diffan.AutomaticXorOrbits.shifts (parityRowSupport k) =
      if k.toNat % 2 = 0 then
        ({0#32, 0x00006000#32} : Finset Word)
      else
        ({0#32} : Finset Word) := by
  by_cases hk : k.toNat % 2 = 0
  · simp only [parityRowSupport, hk, ite_true]
    exact even_shifts_exact
  · simp only [parityRowSupport, hk, ite_false]
    exact odd_shifts_exact

/-- A shift preserving the support of the genuine odd-key DDT row
    must be the identity.  This is stronger than checking sampled keys. -/
theorem odd_key_support_shift_trivial (k t : Word)
    (hk : k.toNat % 2 = 1)
    (hsym : ∀ d : Word,
      (0 < xorDDT_g k (1#32) (d ^^^ t)) ↔
        (0 < xorDDT_g k (1#32) d)) :
    t = (0#32) := by
  have hstable :
      oddOutputSupport.image (fun d => d ^^^ t) = oddOutputSupport := by
    ext d
    constructor
    · intro hd
      obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
      have hpos : 0 < xorDDT_g k (1#32) x :=
        (odd_key_positive_iff_support k x hk).mpr hx
      have htpos := (hsym x).mpr hpos
      rw [hxd] at htpos
      exact (odd_key_positive_iff_support k d hk).mp htpos
    · intro hd
      have hpos : 0 < xorDDT_g k (1#32) d :=
        (odd_key_positive_iff_support k d hk).mpr hd
      have htpos := (hsym d).mpr hpos
      refine Finset.mem_image.mpr
        ⟨d ^^^ t, (odd_key_positive_iff_support k (d ^^^ t) hk).mp htpos, ?_⟩
      bv_decide
  have ht : t ∈ Diffan.AutomaticXorOrbits.shifts oddOutputSupport :=
    (Diffan.AutomaticXorOrbits.mem_shifts_iff
      oddOutputSupport odd_nonempty t).mpr hstable
  rw [odd_shifts_exact] at ht
  exact Finset.mem_singleton.mp ht

end Magma.DiffanUnitInputAutomaticSymmetryAudit
