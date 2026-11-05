module
import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.OneHotTwoHotStructuralZero
public import Magma.Differential.RoundFunction.NibblePairCertificates

@[expose] public section

/-!
# One-hot to two-hot: the second universal middle-nibble obstruction

A three-way partition is used, in order:
  1. Distinct first active nibbles: universally impossible.
  2. Forbidden rotated middle nibble pairs: universally impossible.
  3. Residual pairs: delegated to the exact certified paired-carry refuter.

The finite count of residual triples (1413) is presently computed
separately, not claimed to be a theorem of this module.
-/

namespace Magma.DifanOneHotTwoHotMiddleFilter

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanFirstActiveNibbleInvariant
open Magma.DifanOneHotStructuralZero
open Magma.DifanOneHotTwoHotStructuralZero
open Magma.DifanFiveRoundUniversalSupport
open Magma.DifanPairedCarryRefutation
open Magma.DifanNibblePairCertificates
open Magma.TwoHotOutputOneFirstActive

private abbrev Word := V 32

/-- A first-output-nibble/middle-nibble pair rejected by one of
    the 32 bitvector certificates proved earlier. -/
def BadOneTwoMiddle (i j k : Fin 32) : Prop :=
  ∃ t : Fin 8,
    FirstActiveNibbleAt
      ((Magma.xor (twoHot j k) (oneHotDifference i)).rotateRight 11) t ∧
    BadIndex (⟨i.val / 4, by omega⟩ : Fin 8) t

/-- One general theorem covers every two-hot output whose rotated
    intermediate nibble index is ruled out by the finite blacklist. -/
theorem fiveRound_oneToTwo_zero_of_badMiddle
    (k₀ k₁ k₂ k₃ k₄ : Word)
    (i j k : Fin 32) (hbad : BadOneTwoMiddle i j k) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32) (0#32, twoHot j k) = 0 := by
  obtain ⟨t, ht, hb⟩ := hbad
  exact fiveRound_zero_of_badIndex k₀ k₁ k₂ k₃ k₄
    (oneHotDifference i) (twoHot j k)
    (⟨i.val / 4, by omega⟩ : Fin 8) t
    (oneHot_firstActiveNibble i) ht hb

/-- Only triples escaping both general nibble filters need a
    computationally checked carry-refuter certificate. -/
def ResidualOneToTwoCarryCertificate : Prop :=
  ∀ i j k : Fin 32, j.val < k.val →
    i.val / 4 = j.val / 4 →
    ¬ BadOneTwoMiddle i j k →
    refutesTriple (oneHotDifference i) (twoHot j k) = true

theorem universal_oneToTwo_of_residual_certificate
    (cert : ResidualOneToTwoCarryCertificate)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j k : Fin 32)
    (hjk : j.val < k.val) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32) (0#32, twoHot j k) = 0 := by
  by_cases hfirst : i.val / 4 = j.val / 4
  · by_cases hbad : BadOneTwoMiddle i j k
    · exact fiveRound_oneToTwo_zero_of_badMiddle
        k₀ k₁ k₂ k₃ k₄ i j k hbad
    · exact refutesTriple_sound _ _
        (cert i j k hjk hfirst hbad) k₀ k₁ k₂ k₃ k₄
  · exact fiveRound_oneHot_twoHot_zero_of_different_nibbles
      k₀ k₁ k₂ k₃ k₄ i j k hjk hfirst

theorem universal_twoToOne_of_residual_certificate
    (cert : ResidualOneToTwoCarryCertificate)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j k : Fin 32)
    (hjk : j.val < k.val) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (twoHot j k, 0#32) (0#32, oneHotDifference i) = 0 := by
  rw [← Magma.DifanFiveRoundDDTReverse.outer_ddt_reverse
    k₄ k₃ k₂ k₁ k₀ (oneHotDifference i) (twoHot j k)]
  exact universal_oneToTwo_of_residual_certificate
    cert k₄ k₃ k₂ k₁ k₀ i j k hjk

end Magma.DifanOneHotTwoHotMiddleFilter
