module

public import Difan.Paths.PathCount
public import Difan.Examples.Examples
import all Init.Data.Range.Basic

@[expose] public section

/-!
# Difan.ExamplesPath — a minimal exact-composition example

The two-step cardinality theorem works on the same Boolean toy space
as `Difan.Examples` without any additional probabilistic assumptions.
-/

namespace Difan.ExamplesPath

open Difan
open Difan.Examples

/-- Cardinality of actual two-step Boolean paths, partitioned by the
    exact intermediate difference, using the generic decomposition theorem. -/
example (a c : Bool) :
    composedCount boolSpace boolSpace
      (fun x : Bool => x) (fun x : Bool => x)
      (fun _ => True) (fun _ => True) a c =
    ∑ b : Bool,
      intermediateCount boolSpace boolSpace boolSpace
        (fun x : Bool => x) (fun x : Bool => x)
        (fun _ => True) (fun _ => True) a b c := by
  exact composedCount_eq_sum_intermediate boolSpace boolSpace boolSpace
    (fun x : Bool => x) (fun x : Bool => x)
    (fun _ => True) (fun _ => True) a c

end Difan.ExamplesPath
