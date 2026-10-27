module

public import Magma.UInt8NoPathCertificates
meta import Magma.UInt8NoPathCertificates
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 13: independently certified one-bit exclusions from UInt8 proposals

Iteration 12 introduced a fast UInt8 feasibility scan without assuming its
equivalence to the original Boolean DP. Here each proposed no-path result
is checked against the original `sboxCarryStep` arithmetic and the verified
forward-frontier invariant.

The closed statement below checks the zero-key case `DDT_g(1, 1) = 0`.
The batch evaluation then collects independently certified one-bit `bR`
columns for `aR = 1`. Every accepted column excludes all `aL` for arbitrary
first and third keys, by `certifiedExcludedOneBitBR_sound`.

This is a one-sided soundness result, not full equivalence of the search
implementations. The batch evaluation checks original arithmetic and is
measured separately from the exploratory UInt8 scan.
-/

open Magma.Internal Magma.CarryAutomaton Magma.UInt8NoPathCertificates

namespace Magma.Evidence.UInt8NoPathCertificates

/-- The independent checker accepts this zero-key no-path certificate. -/
theorem zeroKey_bit0_noPath_checked :
    verifyUInt8NoPath (0#32) (1#32) (1#32) = true := by
  decide +kernel

example : xorDDT_g (0#32) (1#32) (1#32) = 0 :=
  verifyUInt8NoPath_sound _ _ _ zeroKey_bit0_noPath_checked

#eval (certifiedExcludedOneBitBR (0#32) (1#32)).map Fin.val

end Magma.Evidence.UInt8NoPathCertificates
