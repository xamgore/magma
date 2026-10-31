module

import all Init.Data.Range.Basic
public import Magma.Diffan.FixedInputMaskedObservation
public import Magma.Diffan.TwoRoundRawOutputMasks
import Std.Tactic.BVDecide

@[expose] public section

/-!
# A 12-bit factor of the reconstructed five-round join observation

With the input difference of the left window fixed, its first common
difference is reconstructed from its base. Its low-box *output
observation* is a function of only
the lowest 12 bits of the first base word. The other 52 base bits are
irrelevant to this observation, for every master key.

This is a factorization of an OBSERVATION, not a claim that the entire
five-round joined count can be aggregated over 12-bit labels. The right
window must still be tested at the reconstructed full point.
-/

namespace Magma.DiffanFixedInputLow12Factor

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundFixedInputGraphJoin
open Magma.DiffanFixedInputMaskedObservation
open Magma.DiffanTwoRoundRawOutputMasks
open Magma.DiffanAutomaticOutputMasks

private abbrev Word :=
  V 32

private abbrev Master :=
  V 256

private abbrev RoundState :=
  Word × Word

/-- Congruence of XOR under a shared output mask. -/
private theorem masked_xor_congr (u v x y mask : Word)
    (hu : (u &&& mask) = (v &&& mask))
    (hx : (x &&& mask) = (y &&& mask)) :
    ((u ^^^ x) &&& mask) = ((v ^^^ y) &&& mask) := by
  bv_decide

/-- Restricting the same XOR sum to a mask preserves equality. -/
private theorem masked_xor_right (u v z mask : Word)
    (h : (u &&& mask) = (v &&& mask)) :
    ((u ^^^ z) &&& mask) = ((v ^^^ z) &&& mask) := by
  exact masked_xor_congr u v z z mask h rfl

/-- The output observation of the derivative depends only on the low 12
bits of its base, even if the two bases differ in arbitrarily many
higher bits. In particular, no special parity of the key is required. -/
theorem derivative_low12_congr (k a u v : Word)
    (h : (u &&& inputLow12Mask) = (v &&& inputLow12Mask)) :
    (gDifference k u a &&& outputLowBoxMask) =
      (gDifference k v a &&& outputLowBoxMask) := by
  let s : Word := u ^^^ v
  have hs : (s &&& inputLow12Mask) = 0#32 := by
    dsimp [s]
    unfold inputLow12Mask at h ⊢
    bv_decide
  have harg : (u ^^^ a) ^^^ s = v ^^^ a := by
    dsimp [s]
    bv_decide
  have hbase : u ^^^ s = v := by
    dsimp [s]
    bv_decide
  have hga := g_outputLowBoxMask_invariant k (u ^^^ a) s hs
  have hgu := g_outputLowBoxMask_invariant k u s hs
  rw [harg] at hga
  rw [hbase] at hgu
  change
    ((g k (u ^^^ a) ^^^ g k u) &&& outputLowBoxMask) =
      ((g k (v ^^^ a) ^^^ g k v) &&& outputLowBoxMask)
  exact masked_xor_congr _ _ _ _ _ hga.symm hgu.symm

/-- The 12-bit input projection is a canonical representative for this
particular observation. No assertion of injectivity is made. -/
def low12Base (b : RoundState) : Word := b.1 &&& inputLow12Mask

/-- Compute only the observed component of the predicted middle
difference. The argument is intended to contain the low 12 base bits. -/
def predictedLow12Value (master : Master) (a : RoundState)
    (low : Word) : Word :=
  (gDifference (roundKey master (0 : Fin 32)) low a.2 ^^^ a.1) &&&
    outputLowBoxMask

/-- The 12-bit observed component factors through `low12Base`.
There is no dependence on the second 32-bit base word. -/
theorem predictedLow12_factor (master : Master)
    (a b : RoundState) :
    ((predictedDelta master a b).2 &&& outputLowBoxMask) =
      predictedLow12Value master a (low12Base b) := by
  have hd := derivative_low12_congr
    (roundKey master (0 : Fin 32)) a.2 b.1
    (b.1 &&& inputLow12Mask) (by
      unfold inputLow12Mask
      bv_decide)
  change
    ((gDifference (roundKey master (0 : Fin 32)) b.1 a.2 ^^^ a.1) &&&
      outputLowBoxMask) =
      ((gDifference (roundKey master (0 : Fin 32))
          (b.1 &&& inputLow12Mask) a.2 ^^^ a.1) &&& outputLowBoxMask)
  exact masked_xor_right _ _ _ _ hd

/-- Explicit compressed observation computed from just the low 12 bits
of the first base word and the fixed input difference. -/
def compressedObservation (master : Master) (a : RoundState)
    (low : Word) : RoundState :=
  (a.2, predictedLow12Value master a low)

/-- The actual masked observation of the reconstructed full midpoint
factors through the 12-bit projection of its base. -/
theorem reconstructed_observation_factors (master : Master)
    (a b : RoundState) :
    observedDifference (0x00006000#32) (reconstructed master a b) =
      compressedObservation master a (low12Base b) := by
  apply Prod.ext
  · rfl
  · change
      ((predictedDelta master a b).2 &&&
        guaranteedMask (0x00006000#32)) =
        predictedLow12Value master a (low12Base b)
    rw [mask_6000_exact]
    exact predictedLow12_factor master a b

/-- The 12-bit input observation determines the masked midpoint
difference, regardless of all other 52 bits of the base. -/
theorem reconstructed_observation_congr (master : Master)
    (a b c : RoundState)
    (h : low12Base b = low12Base c) :
    observedDifference (0x00006000#32) (reconstructed master a b) =
      observedDifference (0x00006000#32) (reconstructed master a c) := by
  rw [reconstructed_observation_factors,
    reconstructed_observation_factors, h]

/-- A concrete reminder: the compressed observation does not determine
the full base, even with a fixed master key and input difference. -/
theorem compressed_observation_noninjective (master : Master)
    (a : RoundState) :
    ∃ b c : RoundState, b ≠ c ∧
      compressedObservation master a (low12Base b) =
        compressedObservation master a (low12Base c) := by
  refine ⟨((0#32), (0#32)), ((0#32), (1#32)), ?_, ?_⟩
  · decide
  · rfl

end Magma.DiffanFixedInputLow12Factor
