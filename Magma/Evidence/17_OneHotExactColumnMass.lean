module

public import Magma.DDT.OneHot.ThreeRound.ExactColumnMass
meta import Magma.DDT.OneHot.ThreeRound.ExactColumnMass
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 17: exact masses within one-bit support classes

The universal support classification identifies the nonempty one-bit
columns for every key. This iteration asks whether keys in the same
support class also have equal counts.

The kernel-checked theorems `oneHotDP_key1_bit20` and `oneHotDP_key2_bit20`
in `Magma.OneHotExactColumnMass` give counts 512 and 1024, respectively.
The keys share the same support class, so support alone does not determine
multiplicity. Their column masses are proved to be `2^41` and `2^42`.

The evaluations below explore all four potentially active positions for
five keys using the exact original carry DP. They run only when this
iteration is explicitly processed; their outputs have not been recorded.
-/

open Magma.OneHotExactColumnMass

namespace Magma.Evidence.OneHotExactColumnMass

/-- Report exact DDT counts at only the four potentially active positions.
    This evaluates only the original carry DP at bits 20 through 23. -/
def activeNibbleCountProfile (k : V 32) : List (Nat × Nat) :=
  (List.finRange 4).map fun r =>
    let j : Fin 32 := ⟨20 + r.val, by omega⟩
    (j.val, oneHotDPCount k j)

#eval activeNibbleCountProfile (0#32)

#eval activeNibbleCountProfile (1#32)

#eval activeNibbleCountProfile (2#32)

#eval activeNibbleCountProfile (0x00800000#32)

#eval activeNibbleCountProfile (0x00800001#32)

end Magma.Evidence.OneHotExactColumnMass
