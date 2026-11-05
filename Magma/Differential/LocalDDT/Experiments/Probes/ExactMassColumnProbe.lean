module

import all Init.Data.Range.Basic
public import Magma.Differential.LocalDDT.PositiveDefectConcreteWitness

@[expose] public section

/-!
# Exact three-round coupling mass at the exceptional prefix

On the already certified exceptional example (aL=0x000CE800, k1=0),
for any odd k0, the two-function convolution is supported at exactly
three intermediate differences. Their exact weights are 2^50, 2^51,
and 2^46. Consequently its total mass is 49*2^46, and the selected
bR=0x00300000 has exact defect 33*2^46.

The finite certificate checks the odd-row prefix fiber, containing at
most 29 candidates, through products of eight local S-box DDT entries.
-/

namespace Magma.DifanExactPositiveDefectMass

open Magma
open Magma.MultiRoundDDT
open Magma.CarryAutomaton
open Magma.OddUnitInput77
open Magma.DifanPositiveDefectConcreteWitness
open Magma.DifanZeroLeftSupportOverlap
open Magma.DifanOddUnitLow20CollisionClasses
open Magma.DifanThreeRoundCouplingDefect

private abbrev Word := V 32

/-- Product of the eight local S-box DDT coefficients for output one. -/
def localColumnCount (c : Word) : Nat :=
  ∏ i : Fin 8,
    SBoxProperties.ddt i (wordDigits c i) (wordDigits (0x00200000#32) i)

/-- This pre-rotation output becomes 1 under the RFC 11-bit rotation. -/
private theorem rot_target : rot11 (0x00200000#32) = (1#32) := by decide

/-- Symbolic bridge, valid for *every* 32-bit input difference. -/
theorem zeroKey_column_eq_local (c : Word) :
    xorDDT_g (0#32) c (1#32) = localColumnCount c := by
  rw [← rot_target, xorDDT_g_zero_key_factor]
  rfl

set_option maxHeartbeats 5000 in
set_option trace.profiler true in
set_option trace.profiler.threshold 10 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
set_option trace.Meta.synthInstance true in
/-- Each of the three supported column entries has count 2^29. -/
theorem three_column_exact :
    xorDDT_g (0#32) candidate0 (1#32) = 2 ^ 29 ∧
    xorDDT_g (0#32) candidate1 (1#32) = 2 ^ 29 ∧
    xorDDT_g (0#32) candidate2 (1#32) = 2 ^ 29 := by
  simp only [zeroKey_column_eq_local, localColumnCount]
  decide +kernel


end Magma.DifanExactPositiveDefectMass
