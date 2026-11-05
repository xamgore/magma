module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundCoreDefect

@[expose] public section

/-!
# Five ordinary Magma rounds: eliminate the central Z coordinate by gEquiv

This is a REINDEXING, not yet a fast implementation. The exact central
base Z is replaced by the genuine middle round-function OUTPUT h=g[k2](Z).
Because g[k2] is bijective, no multiplicity or Jacobian appears.
-/

namespace Magma.DiffanFiveRoundImageJoin

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect

private abbrev Word :=
  V 32

/-- The unique middle-coordinate base that produces a prescribed g-output. -/
noncomputable def middlePreimage (key h : Word) : Word :=
  (gEquiv key).symm h

/-- The three-round feasibility condition indexed by h=g[k2](Z), not Z.
It preserves all original coupled nonlinear conditions. -/
noncomputable def imageJoinCondition (k₁ k₂ k₃ a b : Word)
    (r h : Word) : Prop :=
  threeRoundCoupled k₁ k₂ k₃ (0#32) a b (0#32)
    r ((gEquiv k₂).symm h)

open scoped Classical in
/-- All five-round witnesses can be counted over (r,h), with NO
independent round-DDT multiplication. -/
theorem fiveRound_eq_imageJoin (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, b) =
      ∑ r : Word, ∑ h : Word,
        if imageJoinCondition k₁ k₂ k₃ a b r h
        then (1 : Nat) else 0 := by
  classical
  rw [fiveRound_eq_threeCore, xorDDT_rounds_three_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Fintype.sum_equiv (gEquiv k₂)
  intro z
  have hz : (gEquiv k₂).symm ((gEquiv k₂) z) = z :=
    (gEquiv k₂).symm_apply_apply z
  simp only [imageJoinCondition, hz]

/-- Same equation in the form of three simultaneous constraints.
The first and third are ordinary g derivative fibers; the middle
condition references an inverse image of the central g output. -/
noncomputable def imageTripleCondition (k₁ k₂ k₃ a b : Word)
    (r h : Word) : Prop :=
  let c := gDifference k₁ r a
  xor (gDifference k₂ (middlePreimage k₂ h) c) a = b ∧
    gDifference k₃ (xor h r) b = c

/-- The exact standard Feistel-coupled predicate is the triple condition. -/
theorem imageJoin_iff_three_conditions
    (k₁ k₂ k₃ a b r h : Word) :
    imageJoinCondition k₁ k₂ k₃ a b r h ↔
      imageTripleCondition k₁ k₂ k₃ a b r h := by
  unfold imageJoinCondition imageTripleCondition middlePreimage
    threeRoundCoupled
  have hinv : g k₂ ((gEquiv k₂).symm h) = h :=
    (gEquiv k₂).apply_symm_apply h
  simp only [Magma.xor, BitVec.xor_eq, BitVec.xor_zero, BitVec.zero_xor, hinv]

open scoped Classical in
/-- The genuine triple-join version, with its three constraints visible. -/
theorem fiveRound_eq_imageTriple (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, b) =
      ∑ r : Word, ∑ h : Word,
        if imageTripleCondition k₁ k₂ k₃ a b r h
        then (1 : Nat) else 0 := by
  rw [fiveRound_eq_imageJoin]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact if_congr
    (imageJoin_iff_three_conditions k₁ k₂ k₃ a b r h) rfl rfl

end Magma.DiffanFiveRoundImageJoin
