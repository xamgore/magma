module

public import Diffan.ChainAPI
public import Magma.DiffanBridge
import all Init.Data.Range.Basic

@[expose] public section

/-!
This is an example of composition of g-functions on 32-bit words. It is NOT
a claim that two `g` calls are the same as two 64-bit Feistel rounds.
-/

namespace Magma.DiffanChainExample

open Magma
open Magma.DiffanBridge

/-- Two sequential keyed nonlinear 32-bit functions. -/
def twoFunctions (k₀ k₁ : V 32) : Diffan.Chain (V 32) :=
  Diffan.Chain.cons (g k₀) (Diffan.Chain.cons (g k₁) Diffan.Chain.nil)

/-- The new object-oriented chain API is definitionally the old execution. -/
theorem twoFunctions_run (k₀ k₁ x : V 32) :
    (twoFunctions k₀ k₁).run x = g k₁ (g k₀ x) := rfl

/-- The propagated difference refers to the *same actual base state*. -/
theorem twoFunctions_difference (k₀ k₁ x a : V 32) :
    ((twoFunctions k₀ k₁).propagate xor32 x a).2 =
      Diffan.derivative xor32 xor32 (twoFunctions k₀ k₁).run a x :=
  Diffan.Chain.propagate_snd xor32 (twoFunctions k₀ k₁) x a

/-- Exactly two observations, not one pair of independent DDT entries. -/
theorem twoFunctions_trace_length (k₀ k₁ x a : V 32) :
    ((twoFunctions k₀ k₁).trace xor32 x a).length = 2 := by
  simpa [twoFunctions, Diffan.Chain.cons, Diffan.Chain.nil] using
    (Diffan.Chain.trace_length xor32 (twoFunctions k₀ k₁) x a)

end Magma.DiffanChainExample
