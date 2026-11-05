module

public import Diffan.Paths.Simulation
public import Magma.Carry.Automaton
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Magma.DiffanBridge — 32-bit XOR differences as a Diffan instance

This file adds a dependency Magma -> Diffan, never Diffan -> Magma.
It proves that the existing `xorDDT_g` is *exactly* Diffan's abstract DDT.
-/

namespace Magma.DiffanBridge

open Magma
open Magma.CarryAutomaton

/-- XOR difference structure on Magma's actual 32-bit state words. -/
def xor32 : Diffan.DifferenceSpace (V 32) (V 32) where
  shift := Magma.xor
  diff := Magma.xor
  shift_diff := by
    intro x y
    change x ^^^ (x ^^^ y) = y
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  diff_shift := by
    intro x a
    change x ^^^ (x ^^^ a) = a
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The abstract derivative is the existing XOR round-function
    difference (the two XOR operands are symmetric). -/
theorem derivative_g (k d x : V 32) :
    Diffan.derivative xor32 xor32 (g k) d x =
      Magma.xor (g k (Magma.xor x d)) (g k x) := by
  change Magma.xor (g k x) (g k (Magma.xor x d)) =
    Magma.xor (g k (Magma.xor x d)) (g k x)
  change (g k x) ^^^ (g k (Magma.xor x d)) =
    (g k (Magma.xor x d)) ^^^ (g k x)
  exact BitVec.xor_comm _ _

/-- Equality of the abstract DDT and the existing round-function DDT. -/
theorem ddt_g_eq_existing (k d b : V 32) :
    Diffan.ddt xor32 xor32 (g k) d b =
      xorDDT_g k d b := by
  unfold Diffan.ddt xorDDT_g
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [derivative_g]

end Magma.DiffanBridge
