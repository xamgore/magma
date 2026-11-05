module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundCoreDefect
public import Magma.Differential.ThreeRounds.ThreeRoundZeroRightInputFactorization

@[expose] public section

/-!
# Exact three-round factorization for the middle diagonal

For *three ordinary Feistel G rounds*, suppose the left output difference
is equal to the right input difference: bL=aR. The middle round-function
input difference is forced to zero by the injectivity of g[k1]. An exact
change of coordinates then separates the FIRST and LAST round-function
DDT fibers:

 D3 ((aL,aR),(aR,bR)) = D_g[k0](aR,aL) * D_g[k2](aR,bR).

The middle key k1 disappears. A direct five-round consequence is that
D5 ((a,0),(0,a)) = 0 whenever a != 0, independently of all round keys.
-/

namespace Magma.DiffanThreeRoundMiddleDiagonal

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanThreeRoundCouplingDefect

private abbrev Word :=
  V 32

private abbrev State :=
  FeistelState

/-- XOR of two words is zero exactly when the words agree. -/
private theorem xor_eq_zero_iff_eq (u v : Word) :
    xor u v = (0#32) ↔ u = v := by
  change (u ^^^ v = (0#32)) ↔ u = v
  constructor
  · intro h
    have hh := congrArg (fun w : Word => w ^^^ v) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero, BitVec.zero_xor] using hh
  · intro h
    rw [h]
    exact BitVec.xor_self

/-- The concrete XOR derivative of a bijective round function vanishes
    if and only if its input difference vanishes. -/
theorem gDifference_zero_iff (k x d : Word) :
    gDifference k x d = (0#32) ↔ d = (0#32) := by
  constructor
  · intro h
    have hEq : g k (xor x d) = g k x := by
      exact (xor_eq_zero_iff_eq _ _).mp h
    have hx : xor x d = x := (g_is_bijective k).injective hEq
    have hh := congrArg (fun w : Word => xor x w) hx
    change (x ^^^ (x ^^^ d)) = (x ^^^ x) at hh
    simpa only [← BitVec.xor_assoc, BitVec.xor_self,
      BitVec.zero_xor] using hh
  · intro h
    subst d
    exact Magma.DiffanThreeRoundZeroRightInputFactorization.gDifference_zero k x

/-- For every u, u XOR a = a iff u=0. -/
private theorem xor_right_eq_right_iff (u a : Word) :
    xor u a = a ↔ u = (0#32) := by
  change (u ^^^ a = a) ↔ u = (0#32)
  constructor
  · intro h
    have hh := congrArg (fun w : Word => w ^^^ a) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero] using hh
  · intro h
    rw [h]
    exact BitVec.zero_xor

/-- With bL=aR, the middle differential constraint forces C=0.
    Thus the first and last round function tests are the only ones left. -/
theorem middleDiagonal_separates
    (k₀ k₁ k₂ aL aR bR R Z : Word) :
    threeRoundCoupled k₀ k₁ k₂ aL aR aR bR R Z ↔
      (gDifference k₀ R aR = aL ∧
        gDifference k₂ (xor (g k₁ Z) R) aR = bR) := by
  let C : Word := xor (gDifference k₀ R aR) aL
  have hC : C = (0#32) ↔ gDifference k₀ R aR = aL := by
    exact xor_eq_zero_iff_eq _ _
  have hM : xor (gDifference k₁ Z C) aR = aR ↔ C = (0#32) :=
    (xor_right_eq_right_iff _ _).trans (gDifference_zero_iff k₁ Z C)
  change
    (xor (gDifference k₁ Z C) aR = aR ∧
      gDifference k₂ (xor (g k₁ Z) R) aR = xor bR C) ↔
    (gDifference k₀ R aR = aL ∧
      gDifference k₂ (xor (g k₁ Z) R) aR = bR)
  constructor
  · rintro ⟨hm, hf⟩
    have hc : C = (0#32) := hM.mp hm
    have hfirst := hC.mp hc
    rw [hc] at hf
    change gDifference k₂ (xor (g k₁ Z) R) aR =
      bR ^^^ (0#32) at hf
    simp only [BitVec.xor_zero] at hf
    exact ⟨hfirst, hf⟩
  · rintro ⟨hfirst, hf⟩
    have hc : C = (0#32) := hC.mpr hfirst
    constructor
    · exact hM.mpr hc
    · rw [hc]
      change gDifference k₂ (xor (g k₁ Z) R) aR =
        bR ^^^ (0#32)
      simpa only [BitVec.xor_zero] using hf

/-- Replace (R,Z) with (R,Y), where Y = g[k1](Z) XOR R.
    The map is invertible because g[k1] is a permutation. -/
noncomputable def middleDiagonalCoordinates (k₁ : Word) : State ≃ State where
  toFun p := (p.1, xor (g k₁ p.2) p.1)
  invFun p := (p.1, (gEquiv k₁).symm (xor p.2 p.1))
  left_inv := by
    rintro ⟨R, Z⟩
    apply Prod.ext
    · rfl
    · change (gEquiv k₁).symm ((gEquiv k₁ Z ^^^ R) ^^^ R) = Z
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      exact (gEquiv k₁).symm_apply_apply Z
  right_inv := by
    rintro ⟨R, Y⟩
    apply Prod.ext
    · rfl
    · change ((gEquiv k₁ ((gEquiv k₁).symm (Y ^^^ R))) ^^^ R) = Y
      rw [(gEquiv k₁).apply_symm_apply,
        BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Pointwise separation in the new coordinates. -/
theorem middleDiagonal_separates_coordinates
    (k₀ k₁ k₂ aL aR bR : Word) (p : State) :
    threeRoundCoupled k₀ k₁ k₂ aL aR aR bR p.1 p.2 ↔
      gDifference k₀ (middleDiagonalCoordinates k₁ p).1 aR = aL ∧
      gDifference k₂ (middleDiagonalCoordinates k₁ p).2 aR = bR := by
  exact middleDiagonal_separates k₀ k₁ k₂ aL aR bR p.1 p.2

/-- A bijection between the *actual three-round witnesses* and a
    Cartesian product of first/last round-function DDT witnesses. -/
noncomputable def middleDiagonal_fiberEquiv
    (k₀ k₁ k₂ aL aR bR : Word) :
    {p : State // threeRoundCoupled k₀ k₁ k₂
      aL aR aR bR p.1 p.2} ≃
    {R : Word // gDifference k₀ R aR = aL} ×
    {Y : Word // gDifference k₂ Y aR = bR} :=
  Diffan.CoordinateSeparation.fiberEquiv
    (middleDiagonalCoordinates k₁)
    (fun p => threeRoundCoupled k₀ k₁ k₂
      aL aR aR bR p.1 p.2)
    (fun R => gDifference k₀ R aR = aL)
    (fun Y => gDifference k₂ Y aR = bR)
    (middleDiagonal_separates_coordinates k₀ k₁ k₂ aL aR bR)

/-- THIRD EXACT THREE-ROUND PRODUCT FORMULA. The middle key is irrelevant. -/
theorem threeRound_middleDiagonal_factorization
    (k₀ k₁ k₂ aL aR bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (aR, bR) =
    xorDDT_g k₀ aR aL * xorDDT_g k₂ aR bR := by
  classical
  calc
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, aR) (aR, bR) =
      threeRoundCoupledCount k₀ k₁ k₂ aL aR aR bR :=
      xorDDT_rounds_three k₀ k₁ k₂ aL aR aR bR
    _ = Fintype.card {p : State // threeRoundCoupled
          k₀ k₁ k₂ aL aR aR bR p.1 p.2} := by
      unfold threeRoundCoupledCount
      rw [Fintype.card_subtype]
    _ = Fintype.card {R : Word // gDifference k₀ R aR = aL} *
        Fintype.card {Y : Word // gDifference k₂ Y aR = bR} := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr
        (middleDiagonal_fiberEquiv k₀ k₁ k₂ aL aR bR)
    _ = xorDDT_g k₀ aR aL * xorDDT_g k₂ aR bR := by
      rw [Magma.DiffanThreeRoundZeroRightInputFactorization.gDifference_fiber_card,
        Magma.DiffanThreeRoundZeroRightInputFactorization.gDifference_fiber_card]

/-- Full diagonal slice is independent of the middle key k1. -/
theorem threeRound_independent_middle_key
    (k₀ k₁ k₁' k₂ aL aR bR : Word) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (aR, bR) =
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁' k₂)
      (aL, aR) (aR, bR) := by
  rw [threeRound_middleDiagonal_factorization,
    threeRound_middleDiagonal_factorization]

/-- A bijective g never has zero output difference at nonzero input. -/
theorem xorDDT_g_zero_output_of_nonzero
    (k a : Word) (ha : a ≠ (0#32)) :
    xorDDT_g k a (0#32) = 0 := by
  classical
  unfold xorDDT_g
  have hfalse :
      ((Finset.univ : Finset Word).filter
        (fun x => xor (g k (xor x a)) (g k x) = (0#32))) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.notMem_empty, iff_false]
    intro h
    exact ha ((gDifference_zero_iff k x a).mp h)
  rw [hfalse]
  rfl

/-- The three-round core (0,a) -> (a,0) is impossible for nonzero a. -/
theorem threeRound_diagonal_impossible
    (k₀ k₁ k₂ a : Word) (ha : a ≠ (0#32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (0#32, a) (a, 0#32) = 0 := by
  rw [threeRound_middleDiagonal_factorization,
    xorDDT_g_zero_output_of_nonzero k₀ a ha, zero_mul]

/-- Nontrivial five-round consequence, using BOTH previously
    certified boundary-deletion theorems. -/
theorem fiveRound_diagonal_impossible
    (k₀ k₁ k₂ k₃ k₄ a : Word) (ha : a ≠ (0#32)) :
    xorDDT_rounds 5
      (Magma.DiffanFiveRoundCoreDefect.fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, a) = 0 := by
  rw [Magma.DiffanFiveRoundCoreDefect.fiveRound_eq_threeCore]
  exact threeRound_diagonal_impossible k₁ k₂ k₃ a ha

end Magma.DiffanThreeRoundMiddleDiagonal
