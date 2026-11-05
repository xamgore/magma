module

public import Magma.Search.BatchFamily
meta import Magma.Search.BatchFamily
-- Kernel checks unfold the legacy range loops used by the search code.
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 05: a checked one-bit family and exploratory two-bit search

Research stage: certify a whole family after the shared-base experiment in
`04_BatchCarryGroupedSearch.lean`. Does one accepted base and `List.all` over
the grouped checks establish all 32 one-bit left differences, rather than
only the first accepted candidate?

The fixed base has `k₀ = k₁ = 0`, `aR = 1`, and `bL = 0`. Conditional family
soundness below specializes the general batch theorem; closed Boolean
acceptance is a separate kernel proof. Every resulting zero-DDT statement
quantifies over arbitrary third round keys and right output differences.

The second experiment scans the 496 two-bit differences, then independently
checks prefilter hits. It records outcomes without assuming that any candidate
is impossible. Proposal construction is outside verification timings. Runtime
arguments keep the checked computations inside their measured IO actions.

Build explicitly with `lake build Magma/Evidence/05_BatchFamilyCertificates.lean`.
Earlier iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.BatchSearch Magma.BatchFamily

namespace Magma.Evidence.BatchFamilyCertificates

def exampleBase : SearchBase :=
  { k₀ := 0#32, k₁ := 0#32, aR := 1#32, bL := 0#32 }

/-! ### 2. A family theorem for all 32 one-hot differences -/

/-- Concrete proposal for the 32 one-bit input-left differences. -/
def exampleOneBitBatch : BatchCertificate :=
  { base := exampleBase
    proposal := proposeSearchBase exampleBase
    targets := oneBitDifferences32 }

private theorem oneBitDifferences32_mem (i : Fin 32) :
    BitVec.ofNat 32 (2 ^ i.val) ∈ oneBitDifferences32 := by
  unfold oneBitDifferences32
  apply List.mem_map.mpr
  exact ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩

/-- One Boolean certificate establishes ALL 32 impossible-differential
    claims, not merely the first `aL = 1` candidate. This theorem is
    conditional until the Boolean check itself is proved equal to true. -/
theorem oneBitFamily_impossible_of_checked
    (hchecked : verifyBatchCertificate exampleOneBitBatch = true)
    (i : Fin 32) (k₂ bR : V 32) :
    xorDDT_rounds 3
      (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (2 ^ i.val), (1#32))
      ((0#32), bR) = 0 := by
  have hmember :
      BitVec.ofNat 32 (2 ^ i.val) ∈ exampleOneBitBatch.targets := by
    change BitVec.ofNat 32 (2 ^ i.val) ∈ oneBitDifferences32
    exact oneBitDifferences32_mem i
  exact xorDDT_rounds_three_zero_of_verifiedBatchCertificate
    exampleOneBitBatch (BitVec.ofNat 32 (2 ^ i.val))
    k₂ bR hchecked hmember

set_option maxHeartbeats 0 in
/-- Closed acceptance of the shared base and every one-bit grouped witness. -/
theorem oneBitBatch_checked : verifyBatchCertificate exampleOneBitBatch = true := by
  decide +kernel

/-- All 32 one-bit left differences are impossible for the fixed base,
    for arbitrary third keys and right output differences. -/
theorem oneBitFamily_impossible (i : Fin 32) (k₂ bR : V 32) :
    xorDDT_rounds 3
      (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (2 ^ i.val), (1#32))
      ((0#32), bR) = 0 := by
  exact oneBitFamily_impossible_of_checked oneBitBatch_checked i k₂ bR

/-! ### Diagnostics: grouped costs versus the shared base -/

@[noinline]
private def profileAllOneBitGroupedAt (b : SearchBase) (targets : List (V 32)) : IO Unit := do
  let p := proposeSearchBase b
  let t₀ ← IO.monoMsNow
  let ok := verifyBatchGroupedOnly p targets
  let t₁ ← IO.monoMsNow
  IO.println s!"[family] grouped-only all 32 verified={ok}; time={t₁-t₀}ms"

@[noinline]
private def profileFullOneBitBatchAt (cert : BatchCertificate) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let baseOK := verifySearchBase cert.base cert.proposal
  let t₁ ← IO.monoMsNow
  let groupedOK := verifyBatchGroupedOnly cert.proposal cert.targets
  let t₂ ← IO.monoMsNow
  IO.println s!"[family] base={baseOK}, all-grouped={groupedOK}"
  IO.println s!"[family] base={t₁-t₀}ms, grouped={t₂-t₁}ms"

@[noinline]
private def profileTwoBitFamilyAt (b : SearchBase) (candidates : List (V 32)) : IO Unit := do
  let p := proposeSearchBase b
  let t₀ ← IO.monoMsNow
  let hits := scanAL p candidates
  let t₁ ← IO.monoMsNow
  -- Reuse the existing prefilter results so this stage measures only grouped checking.
  let checked := hits.filter fun aL => verifySearchWiring aL p (proposeWiring aL p)
  let t₂ ← IO.monoMsNow
  IO.println s!"[two-bit] candidates={candidates.length}, fast hits={hits.length}"
  IO.println s!"[two-bit] independently verified={checked.length}"
  IO.println s!"[two-bit] fast scan={t₁-t₀}ms; grouped verifier={t₂-t₁}ms"
  let unverified := candidates.filter fun aL => !(checked.contains aL)
  IO.println s!"[two-bit] unverified aL values={unverified.map BitVec.toNat}"
  match checked.head? with
  | some aL =>
    IO.println s!"[two-bit] first verified aL={aL.toNat}"
  | none =>
    IO.println "[two-bit] no independently verified hit"

/-- Check every one-bit grouped witness without repeating the shared base check. -/
def profileAllOneBitGrouped : IO Unit :=
  profileAllOneBitGroupedAt exampleBase oneBitDifferences32

/-- Check the shared base once, then all 32 grouped witnesses. -/
def profileFullOneBitBatch : IO Unit :=
  profileFullOneBitBatchAt exampleOneBitBatch

/-- Explore all two-bit differences and independently check each prefiltered hit. -/
def profileTwoBitFamily : IO Unit :=
  profileTwoBitFamilyAt exampleBase twoBitDifferences32

/-
Recorded run, 2026-10-26:
  [family] grouped-only all 32 verified=true; time=1874ms
  [family] base=true, all-grouped=true
  [family] base=24799ms, grouped=1821ms
  [two-bit] candidates=496, fast hits=493
  [two-bit] independently verified=493
  [two-bit] fast scan=218ms; grouped verifier=31064ms
  [two-bit] first verified aL=3

The one-bit family's acceptance is proved above. The two-bit counts are
execution results, with the shared base checked by the preceding full-batch
profile; no closed theorem for the whole two-bit family is asserted.
The three unverified values were 8392704, 8396800, and 8404992: bit pairs
`(12, 23)`, `(13, 23)`, and `(14, 23)`, indexed from zero. They remain unresolved
by this search. Elapsed times vary between runs. The profiles below print
current results, including unverified values, for follow-up investigation.
-/

#eval profileAllOneBitGrouped

#eval profileFullOneBitBatch

#eval profileTwoBitFamily

end Magma.Evidence.BatchFamilyCertificates
