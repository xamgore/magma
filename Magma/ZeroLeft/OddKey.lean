module

public import Magma.OddUnitInput77
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Exact zero-left coefficients for odd first-round keys

Combine three-round factorization with the complete 77-entry unit-input
row for odd keys. For arbitrary second and third keys, each coefficient
is the tabulated first-round count at `bR XOR aL` times `DDT_g[k₁](bR, 1)`.
Declarations extend `Magma.OddUnitInput77`.
-/

namespace Magma.OddUnitInput77

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT

/-- MAIN RESULT 3: the exact *individual* 3-round DDT coefficient
    for all odd first keys and arbitrary other two round keys. -/
theorem zeroLeft_odd_first_key_exact
    (k₀ k₁ k₂ aL bR : (V 32))
    (hk : k₀.toNat % 2 = 1) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
        (aL, 1#32) (0#32, bR) =
      oddReferenceCount (xor bR aL) *
        xorDDT_g k₁ bR (1#32) := by
  rw [xorDDT_rounds_three_zero_left_factorization,
      odd_key_complete_DDT k₀ (xor bR aL) hk]

end Magma.OddUnitInput77
