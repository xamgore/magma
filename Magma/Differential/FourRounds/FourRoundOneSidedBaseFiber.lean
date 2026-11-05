module

import all Init.Data.Range.Basic
public import Magma.Differential.FourRounds.FourRoundGeneralBoundaryEquations

@[expose] public section

/-!
# A genuinely coupled one-sided four-round boundary slice

For a single Magma master key and four ordinary rounds, consider
input difference `(aL, 0)` and arbitrary output difference `(bL, bR)`.
The full middle difference after two rounds is determined by its base:

  c = aL,
  d = gDifference (roundKey master 1) u aL.

The remaining two boundary equations give a fiber over `(u, v)` alone.
Unlike the rectangular `(aL, 0) -> (0, bR)` slice, the resulting
conditions are generally coupled. No independent-DDT product is assumed.
-/

namespace Magma.DifanFourRoundOneSidedBaseFiber

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFourRoundScheduledMiddleFibers
open Magma.DifanFourRoundGeneralBoundaryEquations

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private theorem gDifference_zero (k x : Word) : gDifference k x (0#32) = (0#32) := by
  change (g k (x ^^^ (0#32))) ^^^ g k x = (0#32)
  simp only [BitVec.xor_zero, BitVec.xor_self]

private theorem xor_eq_zero_iff (x y : Word) : x ^^^ y = (0#32) ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z : Word => z ^^^ y) h
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] using hh
  · rintro rfl
    exact BitVec.xor_self

/-- For `aR = 0`, the complete middle difference `(c,d)` is fixed
once its left base coordinate `u` is chosen. This holds even when the
output-left difference `bL` is nonzero. -/
theorem middle_delta_of_zero_input_right
    (master : Master) (aL bL bR : Word)
    (w : boundaryEquationFiber master aL (0#32) bL bR) :
    w.1.delta =
      (aL, gDifference (roundKey master (1 : Fin 32)) w.1.base.1 aL) := by
  rcases w with ⟨⟨⟨u, v⟩, ⟨c, d⟩⟩, ⟨h1, h2, h3, h4⟩⟩
  have hzero : aL ^^^ c = (0#32) := by
    rw [gDifference_zero] at h3
    exact h3.symm
  have hc : c = aL := ((xor_eq_zero_iff aL c).mp hzero).symm
  have hd : d = gDifference (roundKey master (1 : Fin 32)) u aL := by
    simpa only [hc, BitVec.zero_xor] using h1.symm
  exact Prod.ext hc hd

/-- The exact reduced two-word middle fiber for the one-sided boundary.
The first condition constrains `v` using a difference computed from
`u`; the second couples both base coordinates through the final round. -/
abbrev oneSidedBaseFiber (master : Master)
    (aL bL bR : Word) : Type :=
  {uv : Word × Word //
    gDifference (roundKey master (2 : Fin 32)) uv.2
      (gDifference (roundKey master (1 : Fin 32)) uv.1 aL) =
        bL ^^^ aL ∧
    gDifference (roundKey master (3 : Fin 32))
      (g (roundKey master (2 : Fin 32)) uv.2 ^^^ uv.1) bL =
        bR ^^^ gDifference (roundKey master (1 : Fin 32)) uv.1 aL}

/-- No four-round trajectory is lost or duplicated when the full
middle state-difference fiber is reduced to its 64-bit middle base. -/
def oneSidedBaseEquiv (master : Master) (aL bL bR : Word) :
    boundaryEquationFiber master aL (0#32) bL bR ≃
      oneSidedBaseFiber master aL bL bR where
  toFun := by
    rintro ⟨⟨⟨u, v⟩, ⟨c, d⟩⟩, h⟩
    have hdelta : (c, d) =
        (aL, gDifference (roundKey master (1 : Fin 32)) u aL) :=
      middle_delta_of_zero_input_right master aL bL bR
        ⟨⟨(u, v), (c, d)⟩, h⟩
    have hc : c = aL := congrArg Prod.fst hdelta
    have hd : d =
        gDifference (roundKey master (1 : Fin 32)) u aL :=
      congrArg Prod.snd hdelta
    rcases h with ⟨_, h2, _, h4⟩
    refine ⟨(u, v), ?_⟩
    constructor
    · simpa only [hc, hd] using h2
    · simpa only [hd] using h4
  invFun := by
    rintro ⟨⟨u, v⟩, ⟨h2, h4⟩⟩
    refine ⟨⟨(u, v),
      (aL, gDifference (roundKey master (1 : Fin 32)) u aL)⟩, ?_⟩
    refine ⟨?_, h2, ?_, h4⟩
    · simp only [BitVec.zero_xor]
    · simp only [gDifference_zero, BitVec.xor_self]
  left_inv := by
    rintro ⟨⟨⟨u, v⟩, ⟨c, d⟩⟩, h⟩
    have hdelta : (c, d) =
        (aL, gDifference (roundKey master (1 : Fin 32)) u aL) :=
      middle_delta_of_zero_input_right master aL bL bR
        ⟨⟨(u, v), (c, d)⟩, h⟩
    have hc : c = aL := congrArg Prod.fst hdelta
    have hd : d =
        gDifference (roundKey master (1 : Fin 32)) u aL :=
      congrArg Prod.snd hdelta
    apply Subtype.ext
    cases hc
    cases hd
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- Direct bijection between genuine four-round endpoint pairs and
the reduced, coupled two-word base fiber. It keeps all four scheduled
subkeys tied to the same 256-bit master key. -/
def oneSidedJoinedEquiv (master : Master) (aL bL bR : Word) :
    joined master
      (inputMasked (aL, 0#32) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True) ≃
    oneSidedBaseFiber master aL bL bR :=
  (generalJoinedEquiv master aL (0#32) bL bR).trans
    (oneSidedBaseEquiv master aL bL bR)

open scoped Classical in
/-- Exact four-round count for arbitrary output difference and zero
input-right difference. No independence or marginal-DDT product. -/
theorem oneSided_exact_base_count (master : Master)
    (aL bL bR : Word) :
    Fintype.card (joined master
      (inputMasked (aL, 0#32) (0#32))
      (outputMasked (bL, bR) (0#32)) (fun _ => True)) =
    Fintype.card (oneSidedBaseFiber master aL bL bR) := by
  classical
  exact Fintype.card_congr (oneSidedJoinedEquiv master aL bL bR)

end Magma.DifanFourRoundOneSidedBaseFiber
