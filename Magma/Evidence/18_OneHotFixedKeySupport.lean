module

public import Magma.OneHot.FixedKeySupportAudit
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 18: fixed-key support versus the union over keys

All 76 candidate cells are realizable over the union of round keys.
This iteration asks how many occur together for one fixed key.
The key `0x06120010` attains 72 cells, as certified by
`real_candidate72Key_has_72_cells` in the library.

The local-potential model has ceiling 72, but its relation to the actual
support for arbitrary keys remains a separate proof obligation.
The examples below certify the exact per-nibble support and local maxima,
and reuse the library theorem for the total support count.
-/

open Magma.OneHotFixedKeySupportAudit

/-- Exact support by input nibble at the selected key. -/
example :
    (List.finRange 8).map (positiveCellsInNibble candidate72Key) =
      [10, 7, 9, 9, 10, 11, 7, 9] := by
  decide +kernel

/-- Total support, already certified in the library. -/
example : (fastPositiveCells candidate72Key).card = 72 :=
  candidate72Key_has_72_cells

/-- Independent local maxima with both carries allowed.
The first nibble of a real transition cannot use incoming carry one. -/
example :
    (List.finRange 8).map (fun i =>
      ((List.finRange 16).map
        (fun q => localPotentialCount i q true)).foldl max 0) =
      [11, 8, 9, 9, 10, 11, 7, 9] := by
  decide +kernel
