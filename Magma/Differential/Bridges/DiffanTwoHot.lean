module

public import Magma.Differential.Bridges.DiffanCarryBridge
public import Magma.DDT.TwoHot.OutputOne.Extrema.SevenCoefficientExtrema
import all Init.Data.Range.Basic

@[expose] public section

/-!
# A real Magma result expressed using Diffan's generic DDT.

The adapter reuses the existing TwoHot coefficient bounds and peak characterization.
-/

namespace Magma.DiffanTwoHot

open Magma
open Magma.CarryAutomaton
open Magma.DiffanBridge
open Magma.TwoHotOutputOneFirstActive
open Magma.TwoHotSevenCoefficientExtrema
open Magma.TwoHotOutputOneSevenExactCounts

/-- A certified bound for the exceptional pair, stated purely using
    the cipher-independent DDT interface. -/
theorem cross_bound (k : V 32) :
    Diffan.ddt xor32 xor32 (g k)
      (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) ≤ 2 ^ 28 := by
  rw [ddt_g_eq_existing]
  exact cross_real_coefficient_le_2pow28 k

/-- The extremal key condition is transported to the generic DDT
    *without redoing any nibble/carry proof*. -/
theorem cross_peak_iff (k : V 32) :
    Diffan.ddt xor32 xor32 (g k)
      (twoHot (23 : Fin 32) (24 : Fin 32)) (1#32) = 2 ^ 28 ↔
    crossAllowed (wordDigits k 5) 0 ∧
      (prefixK k = 0 ∨ crossAllowed (wordDigits k 5) 1) := by
  rw [ddt_g_eq_existing]
  exact cross_real_coefficient_eq_2pow28_iff k

end Magma.DiffanTwoHot
