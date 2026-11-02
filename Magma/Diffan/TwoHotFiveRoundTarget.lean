module

public import Magma.Diffan.FirstActiveNibbleInvariant

@[expose] public section

/-!
# Five-round two-hot outer differential: open conjecture

This module defines the *statement* to be proved; it does not claim
or postulate the conjecture as a theorem. The all-UNSAT computational
matrix is evidence, not part of the Lean kernel proof.
-/

namespace Magma.DiffanTwoHotFiveRoundTarget

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect

abbrev Word := V 32

/-- Two distinct bit positions are set in a 32-bit difference. -/
def TwoHot (a : Word) : Prop :=
  ∃ i j : Fin 32, i ≠ j ∧
    a = (BitVec.ofNat 32 (2 ^ i.val)) ^^^ (BitVec.ofNat 32 (2 ^ j.val))

/-- The remaining mathematical goal, currently an OPEN conjecture.
    It is deliberately a definition of a proposition, not a proof. -/
def universalTwoHotFiveRoundZero : Prop :=
  ∀ (k₀ k₁ k₂ k₃ k₄ a s : Word),
    TwoHot a → TwoHot s →
    xorDDT_rounds 5 (fiveRoundKeys k₀ k₁ k₂ k₃ k₄)
      (a, 0#32) (0#32, s) = 0

end Magma.DiffanTwoHotFiveRoundTarget
