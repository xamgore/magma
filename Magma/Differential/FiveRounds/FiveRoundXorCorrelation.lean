module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundCoreDefect
public import Magma.Differential.ThreeRounds.ThreeRoundConditionalSlices
public import Difan.Fibers.XorFiberCorrelation

@[expose] public section

/-!
# An exactly aggregated slice of the five-round differential

Fix five *ordinary* Magma Feistel rounds and boundary differences
(a,0) -> (0,b). By the proven outer-round deletion theorem the exact
five-round coefficient is an exact three-round core count for k1,k2,k3.

For each intermediate DIFFERENCE c, the full two-coordinate core
predicate becomes the intersection of two first-coordinate derivative
fibers, translated by g[k2](Z), subject to a middle-round constraint
on Z. This is an actual reorganization of the exact coupled count,
not an approximate multiplication of DDT coefficients.

For fixed c, one can compute all 2^32 translation correlations with
one XOR FWHT, then sum over the middle-coordinate Z. That amortized
algorithm is not formally verified in this package. In particular, the
formula retains the coupled conditions of the original path count.
-/

namespace Magma.DifanFiveRoundXorCorrelation

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DifanThreeRoundCouplingDefect
open Magma.DifanThreeRoundRightHistogram
open Magma.DifanThreeRoundConditionalSlices
open Magma.DifanFiveRoundCoreDefect

private abbrev Word :=
  V 32

/-- Left derivative fiber at the first round of the three-round core. -/
def leftFiber (k₁ a c : Word) (r : Word) : Prop :=
  gDifference k₁ r a = c

/-- Right derivative fiber at the third round of the core. -/
def rightFiber (k₃ b c : Word) (s : Word) : Prop :=
  gDifference k₃ s b = c

/-- Exact middle-round condition at the fixed intermediate difference c. -/
def middleFiber (k₂ a b c : Word) (z : Word) : Prop :=
  xor (gDifference k₂ z c) a = b

/-- Genuine number of core witnesses with fixed intermediate difference
c. Here r and z are the bijective coordinates from `threeRoundCoupled`,
not independent heuristic DDT witnesses. -/
noncomputable def coreSlice (k₁ k₂ k₃ a b c : Word) : Nat := by
  classical
  exact ∑ r : Word, ∑ z : Word,
    if leftFiber k₁ a c r ∧ middleFiber k₂ a b c z ∧
      rightFiber k₃ b c (r ^^^ g k₂ z) then (1 : Nat) else 0

/-- A natural 64-bit base class for the original five-round
first-common point B=(u,v): its second word v belongs to
the derivative fiber of the second scheduled key k1.  The first word
u is unrestricted, so this is NOT a hand-picked finite cube. -/
def commonBaseClass (k₁ a c : Word) (B : Word × Word) : Prop :=
  leftFiber k₁ a c B.2

/-- Count the full base class, not just surviving five-round trajectories.
It consists of an arbitrary 32-bit first word paired with one member
of the g[k1] derivative fiber. -/
noncomputable def commonBaseClassSize (k₁ a c : Word) : Nat := by
  classical
  exact ∑ B : Word × Word, if commonBaseClass k₁ a c B then 1 else 0

open scoped Classical in
/-- Each derivative-fiber point admits an arbitrary first base word. -/
theorem commonBaseClassSize_eq_ddt (k₁ a c : Word) :
    commonBaseClassSize k₁ a c =
      Fintype.card Word * xorDDT_g k₁ a c := by
  classical
  have hinner :
      (∑ v : Word, if leftFiber k₁ a c v then (1 : Nat) else 0) =
        xorDDT_g k₁ a c := by
    unfold xorDDT_g
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : xor (g k₁ (xor v a)) (g k₁ v) = c
    · simp only [leftFiber, gDifference, h, ite_true]
    · simp only [leftFiber, gDifference, h, ite_false]
  have houter :
      (∑ _u : Word, xorDDT_g k₁ a c) =
        Fintype.card Word * xorDDT_g k₁ a c := by
    simpa only [Finset.card_univ] using
      (Finset.sum_const_nat
        (s := (Finset.univ : Finset Word))
        (m := xorDDT_g k₁ a c)
        (f := fun _ : Word => xorDDT_g k₁ a c)
        (fun _ _ => rfl))
  unfold commonBaseClassSize commonBaseClass
  rw [Fintype.sum_prod_type]
  simp only [hinner]
  exact houter

open scoped Classical in
/-- The same exact c-slice, with all first-coordinate joins aggregated
into a single XOR correlation histogram indexed by a shift. -/
theorem coreSlice_eq_correlation_sum (k₁ k₂ k₃ a b c : Word) :
    coreSlice k₁ k₂ k₃ a b c =
      ∑ z : Word,
        if middleFiber k₂ a b c z then
          Difan.XorFiberCorrelation.correlation
            (leftFiber k₁ a c) (rightFiber k₃ b c) (g k₂ z)
        else 0 := by
  classical
  exact Difan.XorFiberCorrelation.sum_shifted_fibers_as_correlations
    (leftFiber k₁ a c) (rightFiber k₃ b c)
    (middleFiber k₂ a b c) (g k₂)

private theorem xor_cancel_zero (x y : Word) : xor x y = (0#32) ↔ x = y := by
  change (x ^^^ y = (0#32)) ↔ x = y
  constructor
  · intro h
    have hh := congrArg (fun t : Word => t ^^^ y) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] using hh
  · intro h
    subst y
    exact BitVec.xor_self

/-- At fixed c, the actual exact R/Z-filter from the existing three-round
histogram is the same as the triple-fiber predicate. This is the
nontrivial compatibility step: the middle and third constraints remain
coupled by the same concrete r and z. -/
private theorem core_conditions_iff (k₁ k₂ k₃ a b c r z : Word)
    (hc : gDifference k₁ r a = c) :
    (middleCondition k₁ k₂ (0#32) a b (r, z) ∧
      rightOutput k₁ k₂ k₃ (0#32) a b (r, z) = (0#32)) ↔
    (middleFiber k₂ a b c z ∧
      rightFiber k₃ b c (r ^^^ g k₂ z)) := by
  unfold middleCondition rightOutput intermediateDifference
    middleFiber rightFiber
  simp only [Magma.xor] at *
  rw [hc]
  have hzero : BitVec.xor c (0#32) = c := BitVec.xor_zero
  have hcomm :
      BitVec.xor (g k₂ z) r = BitVec.xor r (g k₂ z) :=
    BitVec.xor_comm (g k₂ z) r
  rw [hzero, hcomm]
  exact and_congr_right (fun _ =>
    xor_cancel_zero (gDifference k₃ (r ^^^ g k₂ z) b) c)

open scoped Classical in
/-- The c-th slice of the three-round DDT decomposition counts exactly
the coupled witnesses in the correlation slice. -/
theorem old_slice_eq_coreSlice (k₁ k₂ k₃ a b c : Word) :
    (∑ r : Word,
      if intermediateDifference k₁ (0#32) a r = c then
        conditionalZCount k₁ k₂ k₃ (0#32) a b (0#32) r
      else 0) = coreSlice k₁ k₂ k₃ a b c := by
  classical
  unfold coreSlice
  apply Finset.sum_congr rfl
  intro r _
  have hclass : intermediateDifference k₁ (0#32) a r = c ↔
      leftFiber k₁ a c r := by
    simp [intermediateDifference, leftFiber, Magma.xor, BitVec.xor_zero]
  by_cases hc : leftFiber k₁ a c r
  · have h : intermediateDifference k₁ (0#32) a r = c := hclass.mpr hc
    simp only [h, ite_true]
    unfold conditionalZCount Difan.FiberUniformity.conditionalCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro z _
    have hp := core_conditions_iff k₁ k₂ k₃ a b c r z hc
    simp only [hc, true_and]
    by_cases hcond : middleCondition k₁ k₂ (0#32) a b (r, z) ∧
        rightOutput k₁ k₂ k₃ (0#32) a b (r, z) = (0#32)
    · have hr := hp.mp hcond
      simp only [hcond, hr]
    · have hr : ¬ (middleFiber k₂ a b c z ∧
          rightFiber k₃ b c (r ^^^ g k₂ z)) :=
        fun hright => hcond (hp.mpr hright)
      simp only [hcond, hr, ite_false]
  · have h : ¬ intermediateDifference k₁ (0#32) a r = c :=
      fun hh => hc (hclass.mp hh)
    simp [h, hc]

open scoped Classical in
/-- The exact five-round coefficient as a sum over intermediate fibers.
Each slice fixes the derivative difference shared by the outer rounds
of the three-round core. -/
theorem fiveRound_eq_sum_coreSlices
    (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, b) =
    ∑ c : Word, coreSlice k₁ k₂ k₃ a b c := by
  classical
  rw [fiveRound_eq_threeCore]
  rw [ddt_eq_sum_conditional_slices]
  -- Express each core slice through the conditional count at fixed c.
  simp_rw [← old_slice_eq_coreSlice k₁ k₂ k₃ a b]
  -- Both sums are over universal Finsets of the same underlying type.
  -- Extensionality avoids reduction of the potentially different
  -- `Fintype` enumeration terms to gigantic concrete lists.
  apply Finset.sum_congr
  · ext c ; simp only [Finset.mem_univ]
  · intro c _
    apply Finset.sum_congr
    · ext r ; simp only [Finset.mem_univ]
    · intro r _
      by_cases h : intermediateDifference k₁ (0#32) a r = c
      · simp only [h, ite_true]
      · simp only [h, ite_false]

open scoped Classical in
/-- Final exact correlation formula for the entire five-round slice.
There is no claim that the c-sum is already computationally cheap;
this provides the correct interface for a certified fast transform. -/
theorem fiveRound_eq_sum_xor_correlations
    (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, b) =
    ∑ c : Word, ∑ z : Word,
      if middleFiber k₂ a b c z then
        Difan.XorFiberCorrelation.correlation
          (leftFiber k₁ a c) (rightFiber k₃ b c) (g k₂ z)
      else 0 := by
  rw [fiveRound_eq_sum_coreSlices]
  apply Finset.sum_congr rfl
  intro c _
  exact coreSlice_eq_correlation_sum k₁ k₂ k₃ a b c

end Magma.DifanFiveRoundXorCorrelation
