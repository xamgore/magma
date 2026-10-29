module

public import Diffan.ChainSimulation
public import Diffan.ExamplesPath
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Diffan.ExamplesChain — small, human-readable examples for the book

Both examples apply general theorems to Boolean transformation chains.
-/

namespace Diffan.ExamplesChain

open Diffan
open Diffan.Examples

/-- Even a three-step chain of arbitrary Boolean transformations has
    an exact decomposition by the complete list of intermediate differences. -/
example (f g h : Bool → Bool) (a b : Bool) :
    ddt boolSpace boolSpace
      (runChain [f, g, h]) a b =
    ∑ sig : (Fin 3 → Option Bool),
      labeledChainCount boolSpace [f, g, h]
        (fun _ => True) (fun _ => True) a b
        (chainSignature boolSpace [f, g, h] a) sig := by
  exact ddt_chain_eq_sum_signatures boolSpace [f, g, h] a b

/-- This result says exactly how a Boolean observation of a three-step
    chain can be computed without forgetting which state was observed. -/
example (f g h : Bool → Bool)
    (hf : ∀ x, f x = x) (hg : ∀ x, g x = x)
    (hh : ∀ x, h x = x) (x : Bool) :
    runChain [f,g,h] x = x := by
  simp [runChain, hf, hg, hh]

end Diffan.ExamplesChain
