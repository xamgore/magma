module
import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.OneHotStructuralZero
public import Magma.DDT.TwoHot.OutputOne.Support.OutputOneFirstActiveNibble
public import Magma.Differential.FiveRounds.PairedCarryRefutation

@[expose] public section

/-!
# Five-round one-hot to two-hot structural exclusions

No SAT and no complete BitVec enumeration: the first active nibble
of a two-hot difference is the nibble of its lower bit, by an
existing independently proved Magma two-hot theorem.
-/

namespace Magma.DifanOneHotTwoHotStructuralZero

open Magma
open Magma.MultiRoundDDT
open Magma.DifanFiveRoundCoreDefect
open Magma.DifanFirstActiveNibbleInvariant
open Magma.DifanOneHotStructuralZero
open Magma.DifanFiveRoundUniversalSupport
open Magma.DifanPairedCarryRefutation
open Magma.TwoHotOutputOneFirstActive

private abbrev Word :=
  V 32

theorem twoHot_firstActiveNibble (j k : Fin 32) (hjk : j.val < k.val) :
    FirstActiveNibbleAt (twoHot j k) (⟨j.val / 4, by omega⟩ : Fin 8) := by
  constructor
  · intro u hu
    exact twoHot_lower_digits_zero j k hjk u hu
  · exact twoHot_first_digit_nonzero j k hjk

/-- Purely structural five-round zero for one-hot to two-hot
    differences whose first active nibble indices differ. -/
theorem fiveRound_oneHot_twoHot_zero_of_different_nibbles
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j k : Fin 32)
    (hjk : j.val < k.val)
    (hne : i.val / 4 ≠ j.val / 4) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (oneHotDifference i, 0#32) (0#32, twoHot j k) = 0 := by
  apply fiveRound_zero_of_distinct_firstActiveNibble
    k₀ k₁ k₂ k₃ k₄ (oneHotDifference i) (twoHot j k)
    (⟨i.val / 4, by omega⟩ : Fin 8)
    (⟨j.val / 4, by omega⟩ : Fin 8)
  · exact oneHot_firstActiveNibble i
  · exact twoHot_firstActiveNibble j k hjk
  · exact Fin.ne_of_val_ne hne

/-- The remaining certificate needs only same-nibble pairs.
    This includes exactly 1,984 of the 15,872 one-hot/two-hot
    pairs. Further middle-index constraints can prune more. -/
def SameNibbleOneToTwoCertificate : Prop :=
  ∀ i j k : Fin 32, j.val < k.val →
    i.val / 4 = j.val / 4 →
    refutesTriple (oneHotDifference i) (twoHot j k) = true

theorem fiveRound_oneHot_twoHot_zero_of_sameNibble_certificate
    (cert : SameNibbleOneToTwoCertificate) (k₀ k₁ k₂ k₃ k₄ : Word) (i j k : Fin 32)
    (hjk : j.val < k.val) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄) (oneHotDifference i, 0#32) (0#32, twoHot j k) =
      0 := by
  by_cases h : i.val / 4 = j.val / 4
  · exact refutesTriple_sound _ _ (cert i j k hjk h) k₀ k₁ k₂ k₃ k₄
  · exact fiveRound_oneHot_twoHot_zero_of_different_nibbles k₀ k₁ k₂ k₃ k₄ i j k hjk h

/-- Exact Feistel reversal transfers the same generic certificate to
    two-hot to one-hot transitions with reversed round-key order. -/
theorem fiveRound_twoHot_oneHot_zero_of_sameNibble_certificate
    (cert : SameNibbleOneToTwoCertificate)
    (k₀ k₁ k₂ k₃ k₄ : Word) (i j k : Fin 32)
    (hjk : j.val < k.val) :
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (twoHot j k, 0#32) (0#32, oneHotDifference i) = 0 := by
  rw [← Magma.DifanFiveRoundDDTReverse.outer_ddt_reverse
    k₄ k₃ k₂ k₁ k₀ (oneHotDifference i) (twoHot j k)]
  exact fiveRound_oneHot_twoHot_zero_of_sameNibble_certificate
    cert k₄ k₃ k₂ k₁ k₀ i j k hjk

end Magma.DifanOneHotTwoHotStructuralZero
