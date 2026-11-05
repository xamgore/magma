module

import all Init.Data.Range.Basic
public import Magma.Differential.RoundFunction.GNibbleBlockCorrelation

@[expose] public section

/-!
# Exact whole-word XOR correlation of two genuine Magma g fibers

The main result combines the previously verified pointwise four-carry
certificate `GCarryFiberTensor` with a symbolic reindexing of the
32-bit input space into TWO four-nibble (=16-bit) coordinates.

For arbitrary round keys, input XOR differences, unrotated target XOR
differences and a whole-word XOR shift, the 32-bit correlation is a sum
of 4 × 4 products of two 16-bit nibble correlations. The carry-state
indices of the two fibers are INDEPENDENT (two different boundary
states) and are explicitly summed. The high and low shifts come from
the SAME actual 32-bit XOR word; there is no probabilistic assumption.
-/

namespace Magma.DiffanGFiberNibbleCorrelation

open Magma
open Magma.CarryAutomaton
open Magma.DiffanGCarryHalfSplit
open Magma.DiffanGCarryFiberTensor
open Magma.DiffanGNibbleBlockCorrelation
open Diffan.BlockwiseXorCorrelation

private abbrev Word :=
  V 32

private abbrev Digits :=
  Fin 8 → Fin 16

/-- Coordinatewise XOR of eight genuine four-bit digits. -/
def digitsXor (d e : Digits) : Digits :=
  fun i => xorDigit (d i) (e i)

/-- The two halves are a genuine equivalence of the eight-nibble word. -/
def digitsHalvesEquiv : Digits ≃ HalfDigits × HalfDigits where
  toFun d := (lowDigits d, highDigits d)
  invFun p := joinDigits p.1 p.2
  left_inv := joinDigits_low_high
  right_inv := by
    intro ⟨lo, hi⟩
    apply Prod.ext
    · funext i
      exact joinDigits_low lo hi i
    · funext i
      exact joinDigits_high lo hi i

/-- Reindex a real 32-bit word by its low and high 16-bit nibble data. -/
def wordHalvesEquiv : Word ≃ HalfDigits × HalfDigits :=
  wordDigitsEquiv.trans digitsHalvesEquiv

/-- The nibble reindexing respects XOR at EVERY word and shift.
This is the key step: the shift is not an artificial block operation. -/
theorem wordHalves_xor (x h : Word) :
    wordHalvesEquiv (xor x h) =
      pairXor (wordHalvesEquiv x) (wordHalvesEquiv h) := by
  apply Prod.ext
  · funext i
    exact wordDigits_xor x h (lowIndex i)
  · funext i
    exact wordDigits_xor x h (highIndex i)

/-- Coordinate reindexing alone, for ANY two weight functions,
transports real 32-bit XOR-correlation without computing 2^32 points. -/
theorem wordCorr_eq_nibbleBlockCorr
    (f g : Word → Nat) (shift : Word) :
    wordCorr f g shift =
      nibbleBlockCorr
        (fun p => f (wordHalvesEquiv.symm p))
        (fun p => g (wordHalvesEquiv.symm p))
        (wordHalvesEquiv shift) := by
  classical
  unfold wordCorr nibbleBlockCorr
  apply Fintype.sum_equiv wordHalvesEquiv
  intro x
  have hbase : wordHalvesEquiv.symm (wordHalvesEquiv x) = x :=
    wordHalvesEquiv.left_inv x
  have hshift : wordHalvesEquiv.symm
      (pairXor (wordHalvesEquiv x) (wordHalvesEquiv shift)) =
      xor x shift := by
    rw [← wordHalves_xor x shift]
    exact wordHalvesEquiv.left_inv (xor x shift)
  change f x * g (x ^^^ shift) =
    f (wordHalvesEquiv.symm (wordHalvesEquiv x)) *
      g (wordHalvesEquiv.symm
        (pairXor (wordHalvesEquiv x) (wordHalvesEquiv shift)))
  simp only [hbase, hshift, Magma.xor, BitVec.xor_eq]

/-- The indicator of a genuine g fiber with target `rot11 target`.
All fixed values appear explicitly as parameters. -/
def gFiberIndicator (key inputDiff target : Word) (x : Word) : Nat :=
  if xor (g key (xor x inputDiff)) (g key x) = rot11 target
    then 1 else 0

/-- The previously proved concrete carry certificate, now indexed by
TWO 16-bit halves rather than the original 32-bit input. -/
theorem gFiberIndicator_eq_carry_mixture
    (key inputDiff target : Word)
    (p : HalfDigits × HalfDigits) :
    gFiberIndicator key inputDiff target (wordHalvesEquiv.symm p) =
      nibbleMixture
        (fun s : CarryState => lowerIndicator
          (wordDigits key) (wordDigits inputDiff) (wordDigits target) s)
        (fun s : CarryState => upperIndicator
          (wordDigits key) (wordDigits inputDiff) (wordDigits target) s) p := by
  classical
  let x : Word := wordHalvesEquiv.symm p
  have hcert := true_g_fiber_indicator_eq_four_state key inputDiff target x
  have hp : (lowDigits (wordDigits x), highDigits (wordDigits x)) = p := by
    exact wordHalvesEquiv.apply_symm_apply p
  have hlo : lowDigits (wordDigits x) = p.1 := congrArg Prod.fst hp
  have hhi : highDigits (wordDigits x) = p.2 := congrArg Prod.snd hp
  simpa only [gFiberIndicator, nibbleMixture, hlo, hhi] using hcert

/-- MAIN BRIDGE: the actual Magma 32-bit XOR correlation of TWO
conditional derivatives is a sum of SIXTEEN pairwise products of
16-bit nibble-block correlations. Both distinct carry-state indices
are kept; this does NOT multiply marginal full-word DDT counts. -/
theorem genuine_g_fiber_correlation_eq_16bit_blocks
    (key₁ diff₁ target₁ key₂ diff₂ target₂ shift : Word) :
    wordCorr
        (gFiberIndicator key₁ diff₁ target₁)
        (gFiberIndicator key₂ diff₂ target₂) shift =
      ∑ s : CarryState, ∑ t : CarryState,
        halfCorr
          (lowerIndicator (wordDigits key₁) (wordDigits diff₁)
            (wordDigits target₁) s)
          (lowerIndicator (wordDigits key₂) (wordDigits diff₂)
            (wordDigits target₂) t)
          (wordHalvesEquiv shift).1 *
        halfCorr
          (upperIndicator (wordDigits key₁) (wordDigits diff₁)
            (wordDigits target₁) s)
          (upperIndicator (wordDigits key₂) (wordDigits diff₂)
            (wordDigits target₂) t)
          (wordHalvesEquiv shift).2 := by
  classical
  calc
    wordCorr
        (gFiberIndicator key₁ diff₁ target₁)
        (gFiberIndicator key₂ diff₂ target₂) shift =
      nibbleBlockCorr
        (fun p => gFiberIndicator key₁ diff₁ target₁ (wordHalvesEquiv.symm p))
        (fun p => gFiberIndicator key₂ diff₂ target₂ (wordHalvesEquiv.symm p))
        (wordHalvesEquiv shift) :=
          wordCorr_eq_nibbleBlockCorr _ _ shift
    _ = _ := nibbleBlockCorr_of_certificates
      (fun p => gFiberIndicator key₁ diff₁ target₁ (wordHalvesEquiv.symm p))
      (fun p => gFiberIndicator key₂ diff₂ target₂ (wordHalvesEquiv.symm p))
      (fun s => lowerIndicator (wordDigits key₁) (wordDigits diff₁)
        (wordDigits target₁) s)
      (fun s => upperIndicator (wordDigits key₁) (wordDigits diff₁)
        (wordDigits target₁) s)
      (fun s => lowerIndicator (wordDigits key₂) (wordDigits diff₂)
        (wordDigits target₂) s)
      (fun s => upperIndicator (wordDigits key₂) (wordDigits diff₂)
        (wordDigits target₂) s)
      (wordHalvesEquiv shift)
      (gFiberIndicator_eq_carry_mixture key₁ diff₁ target₁)
      (gFiberIndicator_eq_carry_mixture key₂ diff₂ target₂)

end Magma.DiffanGFiberNibbleCorrelation
