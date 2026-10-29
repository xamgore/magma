module

public import Magma.Diffan.DiffanCarryBridge
public import Magma.Composition.ZeroLeft.ParityCompleteSlice
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Magma.DiffanThreeRound — use generic Diffan DDT in a real theorem

Application of stage C: reuse the *already proved* special three-round
zero-left identity, replacing its two Magma-local DDT factors by
Diffan's generic DDT via the verified 32-bit adapter.

This does NOT assert a universal product formula for arbitrary rounds.
-/

namespace Magma.DiffanThreeRound

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.DiffanBridge

/-- Certified three-round factorization with both factors described
    through the cipher-independent Diffan interface.
    The output-left-zero hypothesis is essential. -/
theorem zero_left_factorization
    (k₀ k₁ k₂ aL aR bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys k₀ k₁ k₂)
      (aL, aR) (0#32, bR) =
    Diffan.ddt xor32 xor32 (g k₀) aR (xor bR aL) *
    Diffan.ddt xor32 xor32 (g k₁) bR aR := by
  rw [ddt_g_eq_existing, ddt_g_eq_existing]
  exact xorDDT_rounds_three_zero_left_factorization k₀ k₁ k₂ aL aR bR

end Magma.DiffanThreeRound
