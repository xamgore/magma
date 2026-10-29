module

public import Magma.Composition.MultiRoundDDT
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 09: exact DDT counts from sixteen S-box factors

Following the table-based support predictions in `08_ZeroLeftSupport.lean`,
connect the zero-key round-function DDT to the substitution-layer DDT and its
eight local S-box factors. Applying this twice gives a universal exact formula
for the zero-left-output slice with first two keys zero and any third key:

`DDT₃((aL, aR), (0, bR)) =
  (∏ i, DDTᵢ(digitᵢ(aR), digitᵢ(rotr₁₁(bR XOR aL)))) *
  (∏ i, DDTᵢ(digitᵢ(bR), digitᵢ(rotr₁₁(aR))))`.

The general theorem `Magma.MultiRoundDDT.zeroLeft_three_round_exact_sbox_product`
belongs to the library. Here it reduces the three earlier exceptional masks
to sixteen four-bit DDT factors each. Every count is exactly `2^58` for output
right difference `2^23`, uniformly over the third key. No 32-bit or 64-bit
state space is enumerated, and no independence or Markov assumption is used.

Build explicitly with `lake build Magma/Evidence/09_ZeroLeftExactDDT.lean`.
Earlier iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT

namespace Magma.Evidence.ZeroLeftExactDDT

theorem exceptional_12_23_exact_count (k₂ : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (BitVec.ofNat 32 8392704, 1#32)
        (0#32, BitVec.ofNat 32 8388608) =
      2 ^ 58 := by
  rw [zeroLeft_three_round_exact_sbox_product]
  decide +kernel

theorem exceptional_13_23_exact_count (k₂ : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (BitVec.ofNat 32 8396800, 1#32)
        (0#32, BitVec.ofNat 32 8388608) =
      2 ^ 58 := by
  rw [zeroLeft_three_round_exact_sbox_product]
  decide +kernel

theorem exceptional_14_23_exact_count (k₂ : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂) (BitVec.ofNat 32 8404992, 1#32)
        (0#32, BitVec.ofNat 32 8388608) =
      2 ^ 58 := by
  rw [zeroLeft_three_round_exact_sbox_product]
  decide +kernel

end Magma.Evidence.ZeroLeftExactDDT
