module

import all Init.Data.Range.Basic
public import Magma.Differential.Bridges.DiffanReverseRound
public import Magma.Differential.Core.MultiRoundDDT

@[expose] public section

/-!
# Feistel round counts and inverse differentials

A Feistel derivative fixes the output-left difference to the input-right
one. The remaining constraint is a derivative of `g`, with `2 ^ 32`
choices of the input-left half. Identifying this count with Diffan's DDT
transfers the same formula to the inverse round, exchanging input and
output differences.
-/

namespace Magma.DiffanRoundDDTBridge

open Magma
open Magma.FeistelDDT
open Magma.CarryAutomaton
open Magma.DiffanReverseRound

private abbrev RoundState :=
  V 32 × V 32

/-- Elementary rearrangement, valid for all 32-bit words. -/
private theorem xor_rearrange (u v w d : V 32) :
    (u ^^^ v) ^^^ (w ^^^ (v ^^^ d)) = (w ^^^ u) ^^^ d := by
  calc
    (u ^^^ v) ^^^ (w ^^^ (v ^^^ d)) =
        (v ^^^ v) ^^^ ((w ^^^ u) ^^^ d) := by ac_rfl
    _ = (w ^^^ u) ^^^ d := by
      simp only [BitVec.xor_self, BitVec.zero_xor]

/-- The Feistel derivative separates the swapped right half from the
    nonlinear derivative in the other half. -/
theorem derivative_G_eq_feistel (k : V 32) (a x : RoundState) :
    Diffan.derivative roundXor roundXor (G k) a x =
      feistelXorDiff k a.1 a.2 x.1 x.2 := by
  rcases a with ⟨dL, dR⟩
  rcases x with ⟨L, R⟩
  rw [feistelXorDiff_eq]
  apply Prod.ext
  · change R ^^^ (R ^^^ dR) = dR
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · change
      (g k R ^^^ L) ^^^ (g k (R ^^^ dR) ^^^ (L ^^^ dL)) =
        (g k (R ^^^ dR) ^^^ g k R) ^^^ dL
    exact xor_rearrange (g k R) L (g k (R ^^^ dR)) dL

/-- Counting concrete round derivatives gives the Feistel DDT. -/
theorem ddt_G_eq_xorDDT_G (k : V 32) (a b : RoundState) :
    Diffan.ddt roundXor roundXor (G k) a b = xorDDT_G k a b := by
  unfold Diffan.ddt xorDDT_G
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [derivative_G_eq_feistel]

/-- Inverse-round witnesses have the forward count with exchanged differences. -/
theorem inverse_ddt_eq_xorDDT_G (k : V 32) (a b : RoundState) :
    Diffan.ddt roundXor roundXor
      ((GEquiv k).symm : RoundState → RoundState) b a = xorDDT_G k a b := by
  rw [← one_round_ddt_reverse k a b]
  exact ddt_G_eq_xorDDT_G k a b

/-- The exact formula for a *backwards* one-round differential.
    The inverse input-left difference must equal its output-right difference. -/
theorem inverse_ddt_formula (k dL dR eL eR : V 32) :
    Diffan.ddt roundXor roundXor
      ((GEquiv k).symm : RoundState → RoundState)
      (eL, eR) (dL, dR) =
        if eL = dR then
          2 ^ 32 * xorDDT_g k dR (xor eR dL)
        else 0 := by
  rw [inverse_ddt_eq_xorDDT_G]
  exact xorDDT_G_formula k dL dR eL eR

end Magma.DiffanRoundDDTBridge
