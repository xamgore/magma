module

public import Magma.DDT.OneHot.Support.CompleteSupport
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 14: complete one-bit support from independently checked witnesses

Iteration 13 certified zero DDT entries using original carry arithmetic.
Here positive entries are certified too: a backward UInt8 search proposes
an input word, and the original RFC function `g` checks its differential.

For output difference one, the three closed checks classify all 32 one-bit
input differences. Key zero has support `{23}`; keys one and `0x01010101`
have support `{20, 22, 23}`. Indices are counted from the least significant bit.
The checks combine no-path certificates outside the list with concrete
positive witnesses for every listed bit, using kernel computation.

The resulting three-round statements classify empty `bR` columns for right
input difference one, uniformly over the first and third keys. A nonempty
column asserts attainability for some `aL`, not for every `aL`.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.OneHotCompleteSupport

namespace Magma.Evidence.OneHotCompleteSupport

def zeroKeyPossibleBits : List (Fin 32) :=
  [23]

def oneKeyPossibleBits : List (Fin 32) :=
  [20, 22, 23]

def checkZeroKeyOneHot : Bool :=
  verifyOneHotUpperBound (0#32) (1#32) zeroKeyPossibleBits &&
    verifyOneHotLowerBound (0#32) (1#32) zeroKeyPossibleBits

def checkUnitKeyOneHot : Bool :=
  verifyOneHotUpperBound (1#32) (1#32) oneKeyPossibleBits &&
    verifyOneHotLowerBound (1#32) (1#32) oneKeyPossibleBits

def checkPatternKeyOneHot : Bool :=
  verifyOneHotUpperBound (0x01010101#32) (1#32) oneKeyPossibleBits &&
    verifyOneHotLowerBound (0x01010101#32) (1#32) oneKeyPossibleBits

/-- Both inclusions of the zero-key support are checked by the kernel. -/
theorem checkZeroKeyOneHot_checked : checkZeroKeyOneHot = true := by
  decide +kernel

/-- Both inclusions of the unit-key support are checked by the kernel. -/
theorem checkUnitKeyOneHot_checked : checkUnitKeyOneHot = true := by
  decide +kernel

/-- Both inclusions of the repeated-byte-key support are checked by the kernel. -/
theorem checkPatternKeyOneHot_checked : checkPatternKeyOneHot = true := by
  decide +kernel

/-! ### Exact support and three-round column classification -/

/-- Exactly bit 23 has positive round-function DDT for key zero. -/
theorem zeroKey_oneHot_support_exact (i : Fin 32) :
    0 < xorDDT_g (0#32) (oneHot i) (1#32) ↔ i = 23 := by
  have h := Bool.and_eq_true_iff.mp checkZeroKeyOneHot_checked
  simpa only [zeroKeyPossibleBits, List.mem_cons, List.not_mem_nil, or_false] using
    oneHot_g_support_iff (0#32) (1#32) zeroKeyPossibleBits h.1 h.2 i

/-- Exactly bits 20, 22, and 23 have positive round-function DDT for key one. -/
theorem unitKey_oneHot_support_exact (i : Fin 32) :
    0 < xorDDT_g (1#32) (oneHot i) (1#32) ↔
      i = 20 ∨ i = 22 ∨ i = 23 := by
  have h := Bool.and_eq_true_iff.mp checkUnitKeyOneHot_checked
  simpa only [oneKeyPossibleBits, List.mem_cons, List.not_mem_nil, or_false] using
    oneHot_g_support_iff (1#32) (1#32) oneKeyPossibleBits h.1 h.2 i

/-- The repeated-byte key has the same exact one-bit support as key one. -/
theorem patternKey_oneHot_support_exact (i : Fin 32) :
    0 < xorDDT_g (0x01010101#32) (oneHot i) (1#32) ↔
      i = 20 ∨ i = 22 ∨ i = 23 := by
  have h := Bool.and_eq_true_iff.mp checkPatternKeyOneHot_checked
  simpa only [oneKeyPossibleBits, List.mem_cons, List.not_mem_nil, or_false] using
    oneHot_g_support_iff (0x01010101#32) (1#32) oneKeyPossibleBits h.1 h.2 i

/-- With second key zero, exactly bit 23 has a nonempty column. -/
theorem zeroKey_oneHot_columns_exact
    (k₀ k₂ : V 32) (i : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (0#32) k₂)
        (aL, 1#32) (0#32, oneHot i) = 0) ↔ i ≠ 23 := by
  have h := checkZeroKeyOneHot_checked
  unfold checkZeroKeyOneHot at h
  obtain ⟨hu, hl⟩ := Bool.and_eq_true_iff.mp h
  have hiff := oneHot_threeRound_column_zero_iff
    k₀ (0#32) k₂ (1#32) zeroKeyPossibleBits hu hl i
  simpa [zeroKeyPossibleBits] using hiff

/-- With second key one, exactly bits 20, 22, and 23 have nonempty columns. -/
theorem unitKey_oneHot_columns_exact
    (k₀ k₂ : V 32) (i : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (1#32) k₂)
        (aL, 1#32) (0#32, oneHot i) = 0) ↔
      (i ≠ 20 ∧ i ≠ 22 ∧ i ≠ 23) := by
  have h := checkUnitKeyOneHot_checked
  unfold checkUnitKeyOneHot at h
  obtain ⟨hu, hl⟩ := Bool.and_eq_true_iff.mp h
  have hiff := oneHot_threeRound_column_zero_iff
    k₀ (1#32) k₂ (1#32) oneKeyPossibleBits hu hl i
  simpa [oneKeyPossibleBits] using hiff

/-- Same shape of one-bit support for the sampled repeated-byte key. -/
theorem patternKey_oneHot_columns_exact
    (k₀ k₂ : V 32) (i : Fin 32) :
    (∀ aL : V 32,
      xorDDT_rounds 3 (threeRoundKeys k₀ (0x01010101#32) k₂)
        (aL, 1#32) (0#32, oneHot i) = 0) ↔
      (i ≠ 20 ∧ i ≠ 22 ∧ i ≠ 23) := by
  have h := checkPatternKeyOneHot_checked
  unfold checkPatternKeyOneHot at h
  obtain ⟨hu, hl⟩ := Bool.and_eq_true_iff.mp h
  have hiff := oneHot_threeRound_column_zero_iff
    k₀ (0x01010101#32) k₂ (1#32) oneKeyPossibleBits hu hl i
  simpa [oneKeyPossibleBits] using hiff

end Magma.Evidence.OneHotCompleteSupport
