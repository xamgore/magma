module

public import Magma.DDT.UnitInput.Parity
public import Magma.Composition.ZeroLeft.EightEntries
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Zero-left column consequences of first-key parity

At right input difference one, the complete three-round zero-left slice
depends on the first key only through its parity. Combine unit-input row
invariance with column factorization and the known zero-key row: every
even first key has eight equal positive entries in each nonempty column.
The second and third keys and the right output difference remain arbitrary.

Odd first keys reduce to the unit-key reference row; this module does not
classify that row. Declarations extend `Magma.UnitInputParityReduction`.
-/

namespace Magma.UnitInputParityReduction

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.ZeroLeftEightEntries Magma.ZeroLeftColumnTransport

/-! ### IV. New cryptographic corollaries. -/

/-- Exact eight-output row for EVERY even first-round key, not just 0. -/
theorem evenKey_first_row_exact (k d : (V 32))
    (hk : k.toNat % 2 = 0) :
    xorDDT_g k (1#32) d =
      if d ∈ eightOffsets then 2 ^ 29 else 0 := by
  rw [unitInput_DDT_even_key k d hk, zeroKey_first_row_exact]

/-- All three-round zero-left DDT entries with aR=1 now reduce to only
    TWO reference rows (k0=0 and k0=1), for arbitrary k0,k1,k2. -/
theorem zeroLeft_threeRound_parity_reduction
    (k₀ k₁ k₂ bR aL : (V 32)) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) =
      (if k₀.toNat % 2 = 0 then
        xorDDT_g (0#32) (1#32) (xor bR aL)
       else
        xorDDT_g (1#32) (1#32) (xor bR aL)) *
      xorDDT_g k₁ bR (1#32) := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      unitInput_DDT_by_key_parity]

/-- MAIN IMPROVEMENT: the exact eight-equal-entries theorem holds for
    ALL 2^31 even choices of k0, with completely arbitrary k1,k2,bR. -/
theorem zeroLeft_evenFirstKey_exact_eight
    (k₀ k₁ k₂ bR aL : (V 32))
    (hk : k₀.toNat % 2 = 0) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) =
      if xor bR aL ∈ eightOffsets then
        2 ^ 29 * xorDDT_g k₁ bR (1#32)
      else 0 := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      evenKey_first_row_exact k₀ (xor bR aL) hk]
  split_ifs <;> simp

/-- In any nonempty column with even first-round key, there are exactly
    eight positive coefficients, and every one has the same count. -/
theorem zeroLeft_evenFirstKey_positive_iff
    (k₀ k₁ k₂ bR aL : (V 32))
    (hk : k₀.toNat % 2 = 0) :
    0 < xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) ↔
      xor bR aL ∈ eightOffsets ∧
        0 < xorDDT_g k₁ bR (1#32) := by
  rw [zeroLeft_evenFirstKey_exact_eight k₀ k₁ k₂ bR aL hk]
  by_cases h : xor bR aL ∈ eightOffsets
  · simp only [h, ite_true, true_and]
    constructor
    · intro hp
      exact Nat.pos_of_mul_pos_left hp
    · intro hp
      exact Nat.mul_pos (by norm_num) hp
  · simp [h]

/-- Any two first-round keys of the same parity give the SAME complete
    three-round zero-left slice (at right input difference 1), pointwise. -/
theorem zeroLeft_sameParity_firstKeys
    (k₀ k₀' k₁ k₂ bR aL : (V 32))
    (h : k₀.toNat % 2 = k₀'.toNat % 2) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, 1#32) (0#32, bR) =
    xorDDT_rounds 3 (threeRoundKeys k₀' k₁ k₂)
      (aL, 1#32) (0#32, bR) := by
  calc
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR) =
      (if k₀.toNat % 2 = 0 then
          xorDDT_g (0#32) (1#32) (xor bR aL)
       else xorDDT_g (1#32) (1#32) (xor bR aL)) *
        xorDDT_g k₁ bR (1#32) :=
          zeroLeft_threeRound_parity_reduction k₀ k₁ k₂ bR aL
    _ = (if k₀'.toNat % 2 = 0 then
          xorDDT_g (0#32) (1#32) (xor bR aL)
       else xorDDT_g (1#32) (1#32) (xor bR aL)) *
        xorDDT_g k₁ bR (1#32) := by rw [h]
    _ = xorDDT_rounds 3 (threeRoundKeys k₀' k₁ k₂)
        (aL, 1#32) (0#32, bR) :=
          (zeroLeft_threeRound_parity_reduction k₀' k₁ k₂ bR aL).symm

/-- For even first keys, the complete positive first-round support is
    exactly the same eight-offset set as for the zero key. -/
theorem evenKey_first_support_exact (k₀ : (V 32))
    (hk : k₀.toNat % 2 = 0) :
    firstRoundSupport k₀ (1#32) = eightOffsets := by
  classical
  ext d
  simp only [firstRoundSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [evenKey_first_row_exact k₀ d hk]
  by_cases hd : d ∈ eightOffsets <;> simp [hd]

/-- All nonempty zero-left columns with EVEN first key have exactly EIGHT
    positive entries. This extends the zero-key theorem to 2^31 keys. -/
theorem zeroLeft_evenFirstKey_eight_nonzero
    (k₀ k₁ k₂ bR : (V 32))
    (hk : k₀.toNat % 2 = 0)
    (hC : 0 < xorDDT_g k₁ bR (1#32)) :
    (leftColumnSupport k₀ k₁ k₂ (1#32) bR).card = 8 := by
  rw [leftColumnSupport_card_of_pos k₀ k₁ k₂ (1#32) bR hC,
      evenKey_first_support_exact k₀ hk, eightOffsets_card]

end Magma.UnitInputParityReduction
