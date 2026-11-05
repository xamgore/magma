module

public import Difan.Algorithms.KernelFactorization
public import Difan.Examples.ExamplesChain
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.ExamplesWeights — tiny examples for a future book

These small examples separate weighted matrix algebra from the separate
mathematical certificate linking weights to actual DDT trajectories.
-/

namespace Difan.ExamplesWeights

open Difan
open Difan.Examples

/-- Identity weighted relation on two labels. -/
def identityWeight : WeightKernel Bool Bool :=
  fun a b => if a = b then 1 else 0

/-- A trivial weighted relation with multiplicity two on the diagonal. -/
def doubleWeight : WeightKernel Bool Bool :=
  fun a b => if a = b then 2 else 0

/-- Matrix-style convolution can be computed completely on two labels. -/
example : WeightKernel.comp doubleWeight identityWeight true true = 2 := by
  decide

/-- But real DDT composition is handled through *actual fibers*, and
    retains a state-precondition on the chain. -/
example (f g : Bool → Bool) (a b : Bool) :
    ddt boolSpace boolSpace (g ∘ f) a b =
      ∑ mid : Bool,
        intermediateCount boolSpace boolSpace boolSpace f g
          (fun _ => True) (fun _ => True) a mid b := by
  exact ddt_comp_eq_sum_actual_paths boolSpace boolSpace boolSpace f g a b

end Difan.ExamplesWeights
