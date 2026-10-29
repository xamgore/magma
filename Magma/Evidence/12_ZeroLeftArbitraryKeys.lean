module

public import Magma.Composition.MultiRoundDDT
public import Magma.Search.FastSearch
meta import Magma.Composition.MultiRoundDDT
meta import Magma.Search.FastSearch
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 12: zero-left row mass and excluded columns for arbitrary keys

Iteration 11 classified the zero-key slice using conservation of DDT mass.
The arbitrary-key theorems in `Magma.MultiRoundDDT` give total mass `2^64`
for every choice of round keys and right input difference. At fixed `bR`,
the sum over `aL` is `2^32 * xorDDT_g k₁ bR aR`, independent of `k₀` and `k₂`.

A column vanishes exactly when the second-round differential is impossible.
The proved Boolean carry test checks this condition among the 32 one-bit
right output differences, with `aR = 1` and three choices of the second key.
The original three-scan run was interrupted after 356 seconds without a
completed result.

The UInt8 implementation materializes the four reachable carry states at
each nibble, computes successor states directly, and stops on an empty mask.
It is experimental: equivalence to the proved Boolean test has not been
established. Its outputs are search observations, not cryptographic proofs.
The three fast scans run below; reference scans and the five-case comparison
are separate opt-in evaluations because they invoke the slow Boolean DP.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT
open Magma.FastSearch Magma.Certificates.Encoding

namespace Magma.Evidence.ZeroLeftArbitraryKeys

/-- One-bit right output differences whose entire `aL` column vanishes. -/
def excludedOneBitBR (k₁ aR : V 32) : List (Fin 32) :=
  (List.finRange 32).filter (fun i =>
    !xorDiffPossibleBooleanFast k₁ (BitVec.ofNat 32 (2 ^ i.val)) aR)

-- Reference scans; no completed output was recorded.
-- #eval (excludedOneBitBR (0#32) (1#32)).map Fin.val
-- #eval (excludedOneBitBR (1#32) (1#32)).map Fin.val
-- #eval (excludedOneBitBR (0x01010101#32) (1#32)).map Fin.val

/-! ### Materialized four-state UInt8 feasibility scan -/

private def nextCarryMask (i : Fin 8) (keyDigit inputDiff outputDiff : Fin 16) (reachable : UInt8) :
    UInt8 :=
  Id.run do
    let table := fastSboxTables.getD i.val #[]
    let mut result : UInt8 := 0
    for s in [:4] do
      if carryStateMemFast reachable s then
        for x in [:16] do
          let (out, next) := fastSboxCarryStep table keyDigit.val inputDiff.val x s
          if out == outputDiff.val then
            result := result ||| carryStateBitFast next
    return result

/-- Experimental feasibility test. Bit zero encodes the initial carry pair
    `(0, 0)`; final carries are unrestricted modulo `2^32`. -/
def xorDiffPossibleUInt8 (k d b : V 32) : Bool := Id.run do
  if d == (0#32) then
    return b == (0#32)
  let target := b.rotateRight 11
  let mut reachable : UInt8 := 1
  for i in (List.finRange 8) do
    reachable := nextCarryMask i
      (wordDigits k i) (wordDigits d i) (wordDigits target i)
      reachable
    if reachable == 0 then
      return false
  return reachable != 0

/-- One-bit columns rejected by the experimental UInt8 implementation. -/
def excludedOneBitBRUInt8 (k aR : V 32) : List (Fin 32) :=
  (List.finRange 32).filter fun i =>
    !xorDiffPossibleUInt8 k (BitVec.ofNat 32 (2 ^ i.val)) aR

/-- Compare one candidate with the proved Boolean DP. -/
def compareWithOriginalAt (k aR : V 32) (i : Fin 32) : Bool :=
  let bR := BitVec.ofNat 32 (2 ^ i.val)
  xorDiffPossibleUInt8 k bR aR == xorDiffPossibleBooleanFast k bR aR

/-- Sample five bit positions, stopping at the first disagreement. -/
def compareWithOriginalSample (k aR : V 32) : Bool :=
  ([0, 7, 15, 23, 31] : List Nat).all fun j =>
    compareWithOriginalAt k aR (Fin.ofNat 32 j)

/-- Measure the fast 32-candidate scan, excluding output time. -/
@[noinline]
def profileUInt8Scan (k aR : V 32) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let excluded := excludedOneBitBRUInt8 k aR
  let t₁ ← IO.monoMsNow
  IO.println s!"[UInt8] excluded={excluded.length}; bits={excluded.map Fin.val}"
  IO.println s!"[UInt8] 32-candidate scan time={t₁-t₀}ms"

/-- Measure agreement on up to five reference cases, excluding output time. -/
@[noinline]
def profileComparison (k aR : V 32) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let ok := compareWithOriginalSample k aR
  let t₁ ← IO.monoMsNow
  IO.println s!"[UInt8/reference] sampled agreement={ok}"
  IO.println s!"[UInt8/reference] comparison time={t₁-t₀}ms"

#eval profileUInt8Scan (0#32) (1#32)

#eval profileUInt8Scan (1#32) (1#32)

#eval profileUInt8Scan (0x01010101#32) (1#32)

-- Run separately after the fast scans; this invokes the slow reference DP.
-- #eval profileComparison (0#32) (1#32)

end Magma.Evidence.ZeroLeftArbitraryKeys
