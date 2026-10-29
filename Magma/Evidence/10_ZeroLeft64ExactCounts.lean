module

public import Magma.Composition.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 10: exact DDT counts for all 64 predicted pairs

Iteration 08 enumerated pairs using two four-bit S-box tables, and iteration
09 connected the three-round DDT to sixteen exact local factors. Here every
choice `w ∈ W`, `u ∈ U` is certified for first two keys zero, input right
difference one, and an arbitrary third key:

`bR = w * 2^20`, `aL = w * 2^20 + u * 2^11`,

`DDT₃((aL, 1), (0, bR)) = 2 * 16^7 * 2 * 16^7 = 2^58`.

The shifted terms occupy disjoint bits. The proof checks 64 small products
of four-bit DDT entries, without enumerating 32-bit or 64-bit states. The list
has no duplicate pairs, so `sixty_four_certified_pairs` certifies 64 distinct
pairs with identical exact counts, uniformly over the third key.

The reusable list and count proofs live in `Magma.MultiRoundDDT`.
Earlier search profiles are not imported.

Build explicitly with `lake build Magma/Evidence/10_ZeroLeft64ExactCounts.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ZeroLeft64Exact

export Magma.ZeroLeft64Exact (exact_count_for_UW predictedPairs_exact_count predictedPairs_possible
  predictedPairs_nodup sixty_four_certified_pairs)

example (k₂ aL bR : V 32) (hp : (aL, bR) ∈ Magma.ZeroLeftSupport.predictedPairs) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (aL, 1#32) (0#32, bR) = 2 ^ 58 :=
  Magma.ZeroLeft64Exact.predictedPairs_exact_count k₂ aL bR hp

end Magma.Evidence.ZeroLeft64Exact
