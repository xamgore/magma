module

import all Init.Data.Range.Basic
public import Diffan.DifferenceSpace

@[expose] public section

/-!
# Product difference spaces

The difference between two pairs is computed componentwise. A round on
`X × Y` therefore reuses the difference conventions of `X` and `Y`.
No cipher-specific XOR operation is introduced in Diffan.
-/

namespace Diffan.DifferenceSpace

/-- Build differences on a product from independently selected difference
    conventions on both components. -/
def prod {X Y A B : Type*}
    (sx : Diffan.DifferenceSpace X A)
    (sy : Diffan.DifferenceSpace Y B) :
    Diffan.DifferenceSpace (X × Y) (A × B) where
  shift := fun xy ab => (sx.shift xy.1 ab.1, sy.shift xy.2 ab.2)
  diff := fun xy uv => (sx.diff xy.1 uv.1, sy.diff xy.2 uv.2)
  shift_diff := by
    intro xy uv
    apply Prod.ext
    · exact sx.shift_diff xy.1 uv.1
    · exact sy.shift_diff xy.2 uv.2
  diff_shift := by
    intro xy ab
    apply Prod.ext
    · exact sx.diff_shift xy.1 ab.1
    · exact sy.diff_shift xy.2 ab.2

end Diffan.DifferenceSpace
