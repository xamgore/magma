module

public import Magma.OneHotKeyClasses
public import Magma.Evidence.«12_ZeroLeftArbitraryKeys»
meta import Magma.OneHotKeyClasses
meta import Magma.Evidence.«12_ZeroLeftArbitraryKeys»
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 15: local key classes and representative UInt8 comparisons

Iteration 14 introduced two-sided certificates for complete one-bit support.
Here a local RFC S-box calculation predicts support from key nibble five and
the reachability of a common incoming carry. The finite table covers all
32 local classes. The profiler compares one representative per class with
the exploratory UInt8 automaton, without invoking the slow full-word checker.

For key `0x00800000`, the local prediction is empty; its value is fixed below
by kernel computation. This is a statement about the local prediction. The
full-word DDT consequences in `Magma.OneHotKeyClasses` still require independent
certificate acceptance; the representative comparison is experimental.
-/

open Magma.Internal Magma.OneHotKeyClasses

namespace Magma.Evidence.OneHotKeyClasses

theorem predicted_zeroKey :
    (predictedOneHotPositions (0#32)).map Fin.val = [23] := by
  decide

theorem predicted_unitKey :
    (predictedOneHotPositions (1#32)).map Fin.val = [20, 22, 23] := by
  decide

theorem predicted_patternKey :
    (predictedOneHotPositions (0x01010101#32)).map Fin.val = [20, 22, 23] := by
  decide

/-- Key nibble eight with forced zero carry predicts no one-bit support. -/
theorem predicted_emptySupportKey :
    (predictedOneHotPositions (0x00800000#32)).map Fin.val = [] := by
  decide

def fastSupportPositions (k : V 32) : List (Fin 32) :=
  (List.finRange 32).filter fun j =>
    Magma.Evidence.ZeroLeftArbitraryKeys.xorDiffPossibleUInt8
      k (BitVec.ofNat 32 (2 ^ j.val)) (1#32)

/-- 32 representative keys, no large Finset, and no slow verifier. -/
@[noinline]
def profileKeyClasses : IO Unit := do
  let start ← IO.monoMsNow
  let mut passed := 0
  for q in (List.finRange 16) do
    for lower in [false, true] do
      let k := representativeKey q lower
      let prediction := predictedOneHotPositions k
      let observed := fastSupportPositions k
      if prediction == observed then
        passed := passed + 1
      else
        IO.println s!"[key-class] mismatch: q={q.val}, lower={lower}; expected={prediction.map Fin.val}, found={observed.map Fin.val}"
  let finish ← IO.monoMsNow
  IO.println s!"[key-class] UInt8 agreement={passed}/32; time={finish-start}ms"

-- Recorded run: UInt8 agreement=32/32; time=1053ms.
#eval profileKeyClasses

-- Recorded output: []. The theorem above fixes the prediction independently.
#eval (predictedOneHotPositions (0x00800000#32)).map Fin.val

end Magma.Evidence.OneHotKeyClasses
