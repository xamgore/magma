module

public import Magma.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 11: completeness of the 64-pair zero-left slice

Fix the first two keys to zero, the input right difference to one, and the
output left difference to zero. Iteration 10 certified 64 distinct pairs
`(aL, bR)`, each with DDT count `2^58`, uniformly over the third key.

The total mass of this slice is exactly `2^64`. This follows from the row and
column conservation laws of the round-function DDT, using bijectivity of `g`
and XOR translations. Those reusable laws live in `Magma.CarryAutomaton`.
All sums are handled symbolically; no 32-bit or 64-bit universe is enumerated.

The 64 certified pairs exhaust the mass: `64 * 2^58 = 2^64`. Nonnegativity
forces every unlisted entry to zero. The resulting exact classification is
`DDT₃((aL, 1), (0, bR)) = if (aL, bR) ∈ predictedPairs then 2^58 else 0`,
for every third key. Positive support is therefore exactly the earlier list.
The reusable proofs live in `Magma.MultiRoundDDT`.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ZeroLeft64Completeness

export Magma.ZeroLeft64Completeness (zeroLeftSlice zeroLeftSlice_total_mass
  zero_off_saturated_subset known64_total_mass zeroLeftSlice_exact_iff_listed
  zeroLeftSlice_possible_iff_listed)

example (k₂ aL bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (aL, 1#32) (0#32, bR) =
      if (aL, bR) ∈ Magma.ZeroLeftSupport.predictedPairs then 2 ^ 58 else 0 :=
  Magma.ZeroLeft64Completeness.zeroLeftSlice_exact_iff_listed k₂ aL bR

end Magma.Evidence.ZeroLeft64Completeness
