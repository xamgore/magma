module

import all Init.Data.Range.Basic
public import Magma.Diffan.ThreeRoundPeriodSymmetry

@[expose] public section

/-!
# Common-period orbits of three-round conditional fibers

A common XOR period of the first and last round-function derivatives
preserves BOTH the intermediate difference label and the exact conditional
Z-fiber cardinality. Common periods are closed under XOR. Consequently,
they induce an equivalence relation on the first coordinate R.

This module formalizes the orbit relation and a concrete *sufficient*
criterion for full fiber uniformity. It does not assume that every
intermediate-difference class is a single orbit; that is a further,
cipher-specific mathematical question.
-/

namespace Magma.DiffanThreeRoundPeriodOrbits

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundCouplingDefect
open Magma.DiffanThreeRoundConditionalSlices
open Magma.DiffanThreeRoundPeriodSymmetry

private abbrev Word :=
  V 32

/-- The XOR translation h preserves the first and last derivatives
    *globally* (at every concrete base point). -/
def commonPeriod (k₀ k₂ aR bL h : Word) : Prop :=
  (∀ x : Word, gDifference k₀ (xor x h) aR = gDifference k₀ x aR) ∧
  (∀ x : Word, gDifference k₂ (xor x h) bL = gDifference k₂ x bL)

/-- Zero is always a common period. -/
theorem commonPeriod_zero (k₀ k₂ aR bL : Word) :
    commonPeriod k₀ k₂ aR bL (0#32) := by
  constructor
  · intro x
    change gDifference k₀ (x ^^^ (0#32)) aR = gDifference k₀ x aR
    simp only [BitVec.xor_zero]
  · intro x
    change gDifference k₂ (x ^^^ (0#32)) bL = gDifference k₂ x bL
    simp only [BitVec.xor_zero]

/-- Common periods are closed under XOR; this is the crucial
    algebraic fact behind orbit-based compression. -/
theorem commonPeriod_xor
    (k₀ k₂ aR bL h j : Word)
    (hh : commonPeriod k₀ k₂ aR bL h)
    (hj : commonPeriod k₀ k₂ aR bL j) :
    commonPeriod k₀ k₂ aR bL (xor h j) := by
  obtain ⟨hh₀, hh₂⟩ := hh
  obtain ⟨hj₀, hj₂⟩ := hj
  have hx (x : Word) :
      xor x (xor h j) = xor (xor x h) j := by
    change x ^^^ (h ^^^ j) = (x ^^^ h) ^^^ j
    exact (BitVec.xor_assoc x h j).symm
  constructor
  · intro x
    calc
      gDifference k₀ (xor x (xor h j)) aR =
          gDifference k₀ (xor (xor x h) j) aR := by rw [hx x]
      _ = gDifference k₀ (xor x h) aR := hj₀ _
      _ = gDifference k₀ x aR := hh₀ _
  · intro x
    calc
      gDifference k₂ (xor x (xor h j)) bL =
          gDifference k₂ (xor (xor x h) j) bL := by rw [hx x]
      _ = gDifference k₂ (xor x h) bL := hj₂ _
      _ = gDifference k₂ x bL := hh₂ _

/-- Two concrete first coordinates belong to the same common-period orbit
    if the XOR difference between them is a global common period. -/
def samePeriodOrbit (k₀ k₂ aR bL R R' : Word) : Prop :=
  commonPeriod k₀ k₂ aR bL (xor R R')

/-- The common-period orbits form an equivalence relation on R.
    We package the *relation* without introducing another data structure. -/
def periodSetoid (k₀ k₂ aR bL : Word) : Setoid Word where
  r := samePeriodOrbit k₀ k₂ aR bL
  iseqv := by
    constructor
    · intro R
      change commonPeriod k₀ k₂ aR bL (xor R R)
      have hz := commonPeriod_zero k₀ k₂ aR bL
      have heq : xor R R = (0#32) := by
        change R ^^^ R = (0#32)
        exact BitVec.xor_self
      rw [heq]
      exact hz
    · intro R R' h
      change commonPeriod k₀ k₂ aR bL (xor R' R)
      have hc : xor R' R = xor R R' := by
        change R' ^^^ R = R ^^^ R'
        exact BitVec.xor_comm R' R
      rw [hc]
      exact h
    · intro R R' R'' h₁ h₂
      change commonPeriod k₀ k₂ aR bL (xor R R'')
      have h := commonPeriod_xor k₀ k₂ aR bL
        (xor R R') (xor R' R'') h₁ h₂
      have hc : xor (xor R R') (xor R' R'') = xor R R'' := by
        change (R ^^^ R') ^^^ (R' ^^^ R'') = (R ^^^ R'')
        calc
          (R ^^^ R') ^^^ (R' ^^^ R'') =
              R ^^^ (R' ^^^ (R' ^^^ R'')) :=
            BitVec.xor_assoc R R' (R' ^^^ R'')
          _ = R ^^^ ((R' ^^^ R') ^^^ R'') := by
            rw [← BitVec.xor_assoc R' R' R'']
          _ = R ^^^ R'' := by simp only [BitVec.xor_self,
            BitVec.zero_xor]
      rw [hc] at h
      exact h

/-- Period-equivalent concrete first coordinates have the same
    intermediate-difference label. -/
theorem samePeriodOrbit_label
    (k₀ k₂ aL aR bL R R' : Word)
    (h : samePeriodOrbit k₀ k₂ aR bL R R') :
    intermediateDifference k₀ aL aR R =
      intermediateDifference k₀ aL aR R' := by
  obtain ⟨h₀, _⟩ := h
  have ht := intermediateDifference_translate k₀ aL aR (xor R R') R h₀
  have hx : xor R (xor R R') = R' := by
    change R ^^^ (R ^^^ R') = R'
    simp only [← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]
  rw [hx] at ht
  exact ht.symm

/-- Period-equivalent concrete first coordinates have *identical*
    conditional Z-fiber cardinalities at any requested bR. -/
theorem samePeriodOrbit_count
    (k₀ k₁ k₂ aL aR bL bR R R' : Word)
    (h : samePeriodOrbit k₀ k₂ aR bL R R') :
    conditionalZCount k₀ k₁ k₂ aL aR bL bR R =
      conditionalZCount k₀ k₁ k₂ aL aR bL bR R' := by
  obtain ⟨h₀, h₂⟩ := h
  have ht := conditionalZCount_translate
    k₀ k₁ k₂ aL aR bL bR (xor R R') R h₀ h₂
  have hx : xor R (xor R R') = R' := by
    change R ^^^ (R ^^^ R') = R'
    simp only [← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor]
  rw [hx] at ht
  exact ht.symm

/-- Explicit and sufficient criterion for uniformity on each c-fiber:
    choose one representative for every intermediate label and prove that
    every R is in the *same common-period orbit* as its representative.

    Representatives of empty c-fibers are irrelevant. -/
theorem uniform_of_orbit_representatives
    (k₀ k₁ k₂ aL aR bL bR : Word)
    (rep : Word → Word)
    (hrep : ∀ R : Word,
      samePeriodOrbit k₀ k₂ aR bL R
        (rep (intermediateDifference k₀ aL aR R))) :
    ∀ c R : Word, intermediateDifference k₀ aL aR R = c →
      conditionalZCount k₀ k₁ k₂ aL aR bL bR R =
        conditionalZCount k₀ k₁ k₂ aL aR bL bR (rep c) := by
  intro c R hc
  have h := samePeriodOrbit_count k₀ k₁ k₂ aL aR bL bR R
    (rep (intermediateDifference k₀ aL aR R)) (hrep R)
  simpa only [hc] using h

/-- Applying the already-proved conditional-slice factorization is now
    legitimate under the explicit, period-orbit transitivity certificate. -/
theorem weighted_convolution_of_single_orbit_fibers
    (k₀ k₁ k₂ aL aR bL bR : Word)
    (rep : Word → Word)
    (hrep : ∀ R : Word,
      samePeriodOrbit k₀ k₂ aR bL R
        (rep (intermediateDifference k₀ aL aR R))) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (bL, bR) =
    ∑ c : Word, xorDDT_g k₀ aR (xor c aL) *
      conditionalZCount k₀ k₁ k₂ aL aR bL bR (rep c) := by
  exact ddt_eq_weighted_convolution_of_uniform
    k₀ k₁ k₂ aL aR bL bR
    (fun c => conditionalZCount k₀ k₁ k₂ aL aR bL bR (rep c))
    (uniform_of_orbit_representatives k₀ k₁ k₂ aL aR bL bR rep hrep)

/-- For the diagonal slice aR=bL=d the translations by zero and by d
    are always common periods.  This guarantees *paired* orbits, not that
    the entire c-fiber is one orbit. -/
theorem diagonal_period_is_common (k₀ k₂ d : Word) :
    commonPeriod k₀ k₂ d d d := by
  exact ⟨(fun x => gDifference_xor_period k₀ x d),
    (fun x => gDifference_xor_period k₂ x d)⟩

end Magma.DiffanThreeRoundPeriodOrbits
