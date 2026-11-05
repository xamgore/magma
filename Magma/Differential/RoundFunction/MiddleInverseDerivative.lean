module

import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundImageJoin

@[expose] public section

/-!
# The middle image fiber is a genuine derivative fiber of inverse g.

For a bijection e: X≃X on XOR words, conjugating a differential
through e swaps its input and output differences. It does NOT imply
that a derivative of e^{-1} factors in the same nibble coordinates as
one of e; inverse rotation must be represented explicitly.
-/

namespace Magma.DifanMiddleInverseDerivative

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundImageJoin

private abbrev Word :=
  V 32

private theorem xor_rhs_iff (u v w : Word) : xor u v = w ↔ u = xor w v := by
  change (u ^^^ v = w) ↔ (u = w ^^^ v)
  constructor
  · intro h
    have h' := congrArg (fun y : Word => y ^^^ v) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using h'
  · intro h
    calc
      u ^^^ v = (w ^^^ v) ^^^ v := by rw [h]
      _ = w := by simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem xor_pair_cancel (z c : Word) : xor (xor z c) z = c := by
  change (z ^^^ c) ^^^ z = c
  rw [BitVec.xor_assoc, BitVec.xor_comm c z, ← BitVec.xor_assoc]
  simp only [BitVec.xor_self, BitVec.zero_xor]

/-- The XOR derivative of the INVERSE bijection, at actual output h. -/
noncomputable def gInverseDifference (key h diff : Word) : Word :=
  xor ((gEquiv key).symm (xor h diff)) ((gEquiv key).symm h)

/-- Forward fiber at z equals the inverse fiber at its actual image h. -/
theorem forward_iff_inverse_fiber (key z c d : Word) :
    gDifference key z c = d ↔
      gInverseDifference key (g key z) d = c := by
  let e := gEquiv key
  change xor (e (xor z c)) (e z) = d ↔
    xor (e.symm (xor (e z) d)) (e.symm (e z)) = c
  constructor
  · intro h
    have he : e (xor z c) = xor (e z) d := by
      calc
        e (xor z c) = xor d (e z) :=
          (xor_rhs_iff _ _ _).mp h
        _ = xor (e z) d := by
          change d ^^^ (e z) = (e z) ^^^ d
          exact BitVec.xor_comm _ _
    rw [← he, e.symm_apply_apply, e.symm_apply_apply]
    exact xor_pair_cancel z c
  · intro h
    rw [e.symm_apply_apply] at h
    have he : e.symm (xor (e z) d) = xor c z :=
      (xor_rhs_iff _ _ _).mp h
    have he' := congrArg e he
    rw [e.apply_symm_apply] at he'
    apply (xor_rhs_iff _ _ _).mpr
    calc
      e (xor z c) = e (xor c z) := by
        change e (z ^^^ c) = e (c ^^^ z)
        rw [BitVec.xor_comm z c]
      _ = xor (e z) d := he'.symm
      _ = xor d (e z) := by
        change (e z) ^^^ d = d ^^^ (e z)
        exact BitVec.xor_comm _ _

/-- The exact algebraic middle condition on the output h. -/
theorem image_middle_iff_inverse (key c d h : Word) :
    gDifference key (middlePreimage key h) c = d ↔
      gInverseDifference key h d = c := by
  have heq := forward_iff_inverse_fiber key (middlePreimage key h) c d
  have hs : g key (middlePreimage key h) = h :=
    (gEquiv key).apply_symm_apply h
  rw [hs] at heq
  exact heq

/-- An honest *three derivative fibers* predicate: first and third
are forward g; the middle one is a derivative of inverse g. -/
noncomputable def inverseTripleCondition (k₁ k₂ k₃ a b : Word)
    (r h : Word) : Prop :=
  let c := gDifference k₁ r a
  gInverseDifference k₂ h (xor b a) = c ∧
    gDifference k₃ (xor h r) b = c

/-- Inversion reindexes the exact central condition, with no Markov
assumption and no additional witnesses. -/
theorem imageTriple_iff_inverseTriple
    (k₁ k₂ k₃ a b r h : Word) :
    imageTripleCondition k₁ k₂ k₃ a b r h ↔
      inverseTripleCondition k₁ k₂ k₃ a b r h := by
  unfold imageTripleCondition inverseTripleCondition
  have hc : ∀ u : Word, (xor u a = b) ↔ (u = xor b a) :=
    fun u => xor_rhs_iff u a b
  constructor
  · rintro ⟨hm, hr⟩
    exact ⟨(image_middle_iff_inverse k₂
      (gDifference k₁ r a) (xor b a) h).mp
      ((hc _).mp hm), hr⟩
  · rintro ⟨hm, hr⟩
    exact ⟨(hc _).mpr ((image_middle_iff_inverse k₂
      (gDifference k₁ r a) (xor b a) h).mpr hm), hr⟩

open scoped Classical in
/-- Main inverse-derivative form of the exact five-round join. -/
theorem fiveRound_eq_three_inverse_fibers
    (k₀ k₁ k₂ k₃ k₄ a b : Word) :
    Magma.MultiRoundDDT.xorDDT_rounds 5
        (Magma.DifanFiveRoundCoreDefect.fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
        (a, 0#32) (0#32, b) =
      ∑ r : Word, ∑ h : Word,
        if inverseTripleCondition k₁ k₂ k₃ a b r h
        then (1 : Nat) else 0 := by
  rw [fiveRound_eq_imageTriple]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro h _
  exact if_congr
    (imageTriple_iff_inverseTriple k₁ k₂ k₃ a b r h) rfl rfl

end Magma.DifanMiddleInverseDerivative
