module

public import Diffan.Chain
public import Magma.DiffanBridge
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Following an XOR difference through keyed Magma functions

Magma's `g` transforms a 32-bit word. A Feistel round embeds it in an
operation on both halves of a 64-bit block; here we isolate the nonlinear
component. The two subkeys are independent parameters, so the examples
apply to any chosen pair of subkeys.
-/

namespace Magma.DiffanChainExample

open Magma
open Magma.DiffanBridge

def gTwice (k₀ k₁ : V 32) : Diffan.Chain (V 32) :=
  Diffan.Chain.cons (g k₀) (Diffan.Chain.cons (g k₁) Diffan.Chain.nil)

example (k₀ k₁ x : V 32) : (gTwice k₀ k₁).run x = g k₁ (g k₀ x) :=
  rfl

/-- Start with the pair `x` and `x ^^^ a`. At the second call, the base
    word is already `g k₀ x`, and its difference is the first call's output
    difference. Keeping both quantities follows the same pair of executions
    through the whole chain. -/
example (k₀ k₁ x a : V 32) :
    ((gTwice k₀ k₁).propagate xor32 x a).2 =
      Diffan.derivative xor32 xor32 (gTwice k₀ k₁).run a x :=
  Diffan.Chain.propagate_snd xor32 (gTwice k₀ k₁) x a

/-- Trace entries are recorded after each call. The initial difference
    `a` precedes the chain and does not occupy an entry in the trace. -/
example (k₀ k₁ x a : V 32) :
    ((gTwice k₀ k₁).trace xor32 x a).length = 2 := by
  simpa [gTwice, Diffan.Chain.cons, Diffan.Chain.nil] using
    (Diffan.Chain.trace_length xor32 (gTwice k₀ k₁) x a)

end Magma.DiffanChainExample
