module

public import Magma.DDT.TwoHot.OutputOne.Exact.OutputOneSevenExactCounts
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 20: proposed two-hot output-one weighted counts

Fixed-value certificates for `weightedSevenCount`. These concern the
proposed closed formula; its equality with the full DDT still requires
`sevenWeightFiberBridge`.
-/

namespace Magma.TwoHotOutputOneSevenExactCounts

/-- Among the seven universally realizable pairs, zero key realizes
    five with count 2^29, and excludes the remaining two. -/
example :
    weightedSevenCount (0#32) (20,21) = 2 ^ 29 := by decide +kernel

example : weightedSevenCount (0#32) (20, 22) = 0 := by decide +kernel

example : weightedSevenCount (0#32) (23, 24) = 0 := by decide +kernel

/-- The original cross-nibble witness has a positive, exactly
    quantified candidate coefficient. -/
example :
    weightedSevenCount (0x00700000#32) (23,24) = 2 ^ 28 := by decide +kernel

end Magma.TwoHotOutputOneSevenExactCounts
