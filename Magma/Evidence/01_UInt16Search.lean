module

public import Magma.FastSearch
meta import Magma.FastSearch
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 01: UInt16 search and initialization experiments

Research stage: fast search on UInt16 domains. Can local bit deletion find an
impossible three-round differential, and which computations dominate its cost?

For zero first round keys and the candidate `(1, 1) -> (0, bR)`, the sequence
tries single deletions, batching, UInt16 masks, early rejection, and direct
S-box initialization. The bounded fast-initialized search returned `false`;
this reports no certificate within that bound, not a possible differential.
The original single-deletion run exceeded ten minutes without a recorded
result. Historical initialization measurements and comparisons are retained
next to their calls below, including results for readers without Lean.

This motivated the whole-carry-path and grouped-wiring experiments in
`02_CarryGroupedPropagation.lean`. The implementation remains in
`Magma.FastSearch`; this file records the experiments in their original order.
Runs without a transcript have no recorded outcome.

Run explicitly with `lake env lean Magma/Evidence/01_UInt16Search.lean`.
The later iterations do not import or execute these expensive experiments.
-/

open Magma.Internal Magma.CarryAutomaton Magma.MultiRoundDDT Magma.Pruning Magma.Certificates
open Magma.Certificates.Encoding Magma.Certificates.BackwardMask Magma.FastSearch

namespace Magma.Evidence.UInt16Search

/-- Candidate inputs for the original local deletion search.
    These are test *inputs*, not asserted impossible differentials.
    The first manual recipes below have no recorded completed result. -/
def exampleBitDeletionCandidates : List (V 32 × V 32 × V 32) :=
  [ (0#32, 1#32, 0#32),
    (1#32, 1#32, 0#32),
    (0x100#32, 0x1000#32, 0x01000000#32),
    (0x12345678#32, 0x10203040#32, 0x89abcdef#32) ]

-- An earlier evaluation exceeded ten minutes; no result was recorded.
#eval ((generateBitDeletionCertificate (0#32) (0#32) (1#32) (1#32) (0#32) 256).isSome : Bool)

#eval
  (scanThreeRoundBitDeletionCandidates (0#32) (0#32) 256 exampleBitDeletionCandidates :
    Option ((V 32 × V 32 × V 32) × BitDeletionCertificate))

-- Bounded experiments; no evaluation outputs were recorded.
#eval ((generateBatchedBitDeletionCertificate (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome : Bool)

#eval (groupedContradiction (0#32) (0#32) (1#32) (1#32) (0#32) 2 : Bool)

-- Larger-wave experiment; no completed evaluation was recorded.
#eval ((generateUInt16DeletionCertificate (0#32) (0#32) (1#32) (1#32) (0#32) 128).isSome : Bool)

/-! ### One `#eval` can now print separate timings for the individual stages. -/

/-- Run with `#eval profileUInt16Certificate ... 1 false`.

    It prints separate elapsed times for domain initialization, one scan,
    bounded search, and replay. Replay is skipped unless the mask state is
    contradictory OR `forceVerifier = true`.

    This measures runtime of the evaluated expressions, not elaboration,
    compilation, editor delays or the entire Lean process startup time. -/
def profileUInt16Certificate
    (k₀ k₁ aL aR bL : V 32)
    (waves : Nat := 1) (forceVerifier : Bool := false) : IO Unit := do
  IO.println "[0] starting UInt16 certificate benchmark"
  let t0 ← IO.monoMsNow
  let D := bitDomainsToUInt16 (initialBitDomains k₀ k₁ aR bL)
  let initiallyEmpty := emptyUInt16BitDomain D
  -- Printing the result before the timestamp forces evaluation of D.
  IO.println s!"[1] masks built; initially empty={initiallyEmpty}"
  let t1 ← IO.monoMsNow
  IO.println s!"    initialization + conversion: {t1 - t0} ms"

  let firstWave := fastUInt16DeletionWave aL D
  let firstLen := firstWave.2.length
  IO.println s!"[2] first wave: deletions={firstLen}"
  let t2 ← IO.monoMsNow
  IO.println s!"    1024-proposal scan: {t2 - t1} ms"

  let deletions := fastUInt16DeletionLog aL D waves
  let n := deletions.length
  IO.println s!"[3] {waves} bounded waves: logged deletions={n}"
  let t3 ← IO.monoMsNow
  IO.println s!"    search: {t3 - t2} ms"

  let finalD := uint16DomainsAfterDeletions D deletions
  let contradictory := emptyUInt16BitDomain finalD
  IO.println s!"[4] mask replay: empty={contradictory}"
  let t4 ← IO.monoMsNow
  IO.println s!"    replay: {t4 - t3} ms"

  if contradictory || forceVerifier then
    let cert : BitDeletionCertificate := { deletions := deletions }
    let ok := verifyBitDeletionCertificate k₀ k₁ aL aR bL cert
    IO.println s!"[5] original verifier: accepted={ok}"
    let t5 ← IO.monoMsNow
    IO.println s!"    Finset verification: {t5 - t4} ms"
  else
    IO.println "[5] verifier skipped: no empty UInt16 domain"

  IO.println "[done]"

/-
  Profiling experiments. No historical transcript was
  recorded for these calls; timings and outcomes require a completed run.
  Stable recorded checks live in Magma.Evidence.CarryGroupedPropagation.
-/

-- Display a per-stage profile; false avoids unnecessary slow validation.
#eval (profileUInt16Certificate (0#32) (0#32) (1#32) (1#32) (0#32) 1 false : IO Unit)

-- Force the original verifier to measure its cost on the same input.
#eval (profileUInt16Certificate (0#32) (0#32) (1#32) (1#32) (0#32) 1 true : IO Unit)

-- Reject before invoking the expensive verifier.
#eval ((generateUInt16CertificateEarlyReject (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome : Bool)

/-
Purpose: remove Finset/Decidable initial-domain computation from the SEARCH
path (about 38 seconds in the original profiling run). The expensive, proved original certificate checker
remains the only acceptance criterion for positive certificates.

This is search-side code, not a proved replacement for
Magma.Pruning.nibbleTransitionPossible. The `fastInitialDomainsAgree`
diagnostic lets you compare the two computations on any chosen input.
-/
/-- Compare the fast search initialization to the SLOW proved Finset-based
    initialization on concrete inputs. This is a runtime diagnostic,
    NOT a universal equality proof; run it once for a test case. -/
def fastInitialDomainsAgree
    (k₀ k₁ aR bL : V 32) : Bool :=
  fastInitialBitDomains k₀ k₁ aR bL ==
    bitDomainsToUInt16 (initialBitDomains k₀ k₁ aR bL)

/-! ### Timing only the fast initialization and search -/

def profileFastInitialCertificate (k₀ k₁ aL aR bL : V 32) (waves : Nat := 8)
    (forceVerifier : Bool := false) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let D := fastInitialBitDomains k₀ k₁ aR bL
  IO.println s!"[fast-init] empty={emptyUInt16BitDomain D}"
  let t₁ ← IO.monoMsNow
  IO.println s!"[fast-init] time={t₁ - t₀} ms"
  let deletions := fastUInt16DeletionLog aL D waves
  IO.println s!"[search] deletions={deletions.length}"
  let t₂ ← IO.monoMsNow
  IO.println s!"[search] time={t₂ - t₁} ms"
  let contradictory := emptyUInt16BitDomain (uint16DomainsAfterDeletions D deletions)
  IO.println s!"[replay] empty={contradictory}"
  let t₃ ← IO.monoMsNow
  IO.println s!"[replay] time={t₃ - t₂} ms"
  if contradictory || forceVerifier then
    let cert : BitDeletionCertificate := { deletions := deletions }
    let accepted := verifyBitDeletionCertificate k₀ k₁ aL aR bL cert
    IO.println s!"[old-verifier] accepted={accepted}"
    let t₄ ← IO.monoMsNow
    IO.println s!"[old-verifier] time={t₄ - t₃} ms"
  else
    IO.println "[old-verifier] skipped (no contradiction)"

/-
  Historical initialization experiments. These are recorded observations
  from the original research run, not current timing guarantees. The fixed
  observations are also proved in Magma.Evidence.CarryGroupedPropagation.
-/

-- Recorded initialization cost: about 38 sec -> 66 ms.
#eval (profileFastInitialCertificate (0#32) (0#32) (1#32) (1#32) (0#32) 1 false : IO Unit)

-- Evaluation compares both implementations, including the slow path.
#eval (fastInitialDomainsAgree (0#32) (0#32) (1#32) (0#32) : Bool)

-- Recorded output: true; elapsed time: 72 sec.
-- This checks one input; it is not a universal equivalence proof.

-- Return false rapidly if the fast search sees no empty domain.
#eval ((generateFastInitialCertificate (0#32) (0#32) (1#32) (1#32) (0#32) 8).isSome : Bool)

-- Recorded output: false; elapsed time: 35 sec.
-- No certificate was found by this pruning strategy on this input.

end Magma.Evidence.UInt16Search
