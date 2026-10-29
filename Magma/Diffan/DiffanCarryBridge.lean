module

public import Magma.Diffan.DiffanBridge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Magma.DiffanCarryBridge — a certified executable DDT computation

This is the key reuse point: the existing eight-nibble carry dynamic
program implements the generic Diffan DDT. The formula is symbolic,
not an exhaustive evaluation of 32-bit inputs.
-/

namespace Magma.DiffanCarryBridge

open Magma
open Magma.Internal
open Magma.CarryAutomaton
open Magma.DiffanBridge

/-- An executable eight-step count (rather than the huge generic Finset
    cardinality). Rotate the *output difference* back by 11 bits. -/
def fastDDT (k d b : V 32) : Nat :=
  carryDPCount (wordDigits k) (wordDigits d)
    (wordDigits (b.rotateRight 11))

/-- Certified equality between the existing Magma DP and Diffan DDT. -/
theorem fastDDT_correct (k d b : V 32) :
    fastDDT k d b = Diffan.ddt xor32 xor32 (g k) d b := by
  have hrotate :
      fastDDT k d b =
        carryDPCount (wordDigits k) (wordDigits d)
          (wordDigits (unrot11 b)) := by
    simp only [fastDDT, unrot11_eq_rotateRight11]
  calc
    fastDDT k d b =
        carryDPCount (wordDigits k) (wordDigits d)
          (wordDigits (unrot11 b)) := hrotate
    _ = matrixDDT_g k d b := by
      unfold matrixDDT_g
      exact carryDPCount_eq_carryMatrixCount _ _ _
    _ = xorDDT_g k d b := (xorDDT_g_eq_matrixDDT k d b).symm
    _ = Diffan.ddt xor32 xor32 (g k) d b :=
      (ddt_g_eq_existing k d b).symm

/-- First Magma instance of the abstract certified-count interface. -/
def certifiedG :
    Diffan.CertifiedDDT xor32 xor32 (fun k : V 32 => g k) where
  compute := fastDDT
  correct := by
    intro k a b
    exact fastDDT_correct k a b

end Magma.DiffanCarryBridge
