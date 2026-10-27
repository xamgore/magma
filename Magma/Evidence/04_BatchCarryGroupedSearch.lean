module

public import Magma.BatchSearch
meta import Magma.BatchSearch
-- Kernel checks unfold the legacy range loops used by the search code.
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 04: batch carry/grouped search with a shared verified base

Research stage: scaling the concrete three-round result to candidate families.
Can initial coverage and both carry automata be computed and checked once for
fixed `(k₀, k₁, aR, bL)`, then reused while scanning different `aL` values?

Following `03_FastInitialCover.lean`, use transition-based initial coverage
and separate the shared base check from per-candidate grouped verification.
The experiment scans all 32 one-bit left input differences for the same
zero-key base and independently checks the first prefiltered hit.
Prefilter hits alone are search observations; the soundness theorem requires
both the shared base and the individual grouped witness to be accepted.

The three profiles measure proposal/search, shared base verification, and
selection of one independently verified grouped witness separately. Timings
are observations from execution, not fixed assertions or speed guarantees.
Build explicitly with `lake build Magma/Evidence/04_BatchCarryGroupedSearch.lean`.
Earlier iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.FastSearch Magma.BatchSearch

namespace Magma.Evidence.BatchCarryGroupedSearch

def exampleBase : SearchBase :=
  { k₀ := 0#32, k₁ := 0#32, aR := 1#32, bL := 0#32 }

-- Runtime parameters prevent closed proposals from being lifted outside the measured run.
@[noinline]
private def profileBatchSearchAt (b : SearchBase) (aLs : List (V 32)) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let p := proposeSearchBase b
  let t₁ ← IO.monoMsNow
  let hits := scanAL p aLs
  IO.println s!"[batch] one-bit candidates={aLs.length}; hits={hits.length}"
  let t₂ ← IO.monoMsNow
  IO.println s!"[batch] init+carry={t₁-t₀}ms; grouped scan={t₂-t₁}ms"
  IO.println s!"[batch] contains aL=1: {decide ((1#32) ∈ hits)}"
  IO.println s!"[batch] hit aL values={hits.map BitVec.toNat}"

@[noinline]
private def profileBatchBaseVerificationAt (b : SearchBase) : IO Unit := do
  let p := proposeSearchBase b
  let t₀ ← IO.monoMsNow
  let ok := verifySearchBase b p
  IO.println s!"[batch] shared base verified={ok}"
  let t₁ ← IO.monoMsNow
  IO.println s!"[batch] shared base verification={t₁-t₀}ms"

@[noinline]
private def profileBatchFirstVerifiedHitAt (b : SearchBase) (aLs : List (V 32)) : IO Unit := do
  let p := proposeSearchBase b
  let hits := scanAL p aLs
  let t₀ ← IO.monoMsNow
  let first := firstVerifiedAL p hits
  IO.println s!"[batch] first independently verified hit found={first.isSome}"
  let t₁ ← IO.monoMsNow
  IO.println s!"[batch] grouped verification={t₁-t₀}ms"
  match first with
  | some aL =>
    IO.println s!"[batch] first verified aL={aL.toNat}"
  | none =>
    pure ()

/-- Only fast proposal and grouped search; independent verification is measured separately. -/
def profileBatchSearch : IO Unit :=
  profileBatchSearchAt exampleBase oneBitDifferences32

/-- Check the shared base once, separately from construction and per-candidate wiring. -/
def profileBatchBaseVerification : IO Unit :=
  profileBatchBaseVerificationAt exampleBase

/-- Independently verify the first prefiltered hit, excluding proposal and scan time. -/
def profileBatchFirstVerifiedHit : IO Unit :=
  profileBatchFirstVerifiedHitAt exampleBase oneBitDifferences32

set_option maxHeartbeats 0 in
/-- The concrete base is proved once and can be reused for different left differences. -/
theorem sharedBaseChecked :
    verifySearchBase exampleBase (proposeSearchBase exampleBase) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- The first independently accepted candidate is the original `aL = 1` case. -/
theorem firstBatchHitChecked :
    firstVerifiedAL (proposeSearchBase exampleBase)
        (scanAL (proposeSearchBase exampleBase) oneBitDifferences32) = some (1#32) := by
  decide +kernel

/-- End-to-end use of the shared-base theorem for the accepted batch hit. -/
theorem firstBatchHitImpossible (k₂ bR : V 32) :
    xorDDT_rounds 3 (threeRoundKeys (0#32) (0#32) k₂)
      ((1#32), (1#32)) ((0#32), bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_firstVerifiedAL
    exampleBase (proposeSearchBase exampleBase)
    (scanAL (proposeSearchBase exampleBase) oneBitDifferences32)
    (1#32) k₂ bR sharedBaseChecked firstBatchHitChecked

/-
Recorded run, 2026-10-26:
  [batch] one-bit candidates=32; hits=32
  [batch] init+carry=72ms; grouped scan=14ms
  [batch] contains aL=1: true
  [batch] shared base verified=true
  [batch] shared base verification=23153ms
  [batch] first independently verified hit found=true
  [batch] grouped verification=56ms
  [batch] first verified aL=1

The hit list contained every `2^i`, for `i` from 0 through 31. These are
prefilter results; this run independently verifies the shared base and the
first hit. Their acceptance is also proved above. Elapsed times vary between
runs and are not proof obligations. The profiles below print current results.
-/

#eval profileBatchSearch

#eval profileBatchBaseVerification

#eval profileBatchFirstVerifiedHit

end Magma.Evidence.BatchCarryGroupedSearch
