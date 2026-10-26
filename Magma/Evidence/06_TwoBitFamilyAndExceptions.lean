module

public import Magma.BatchFamily
meta import Magma.BatchFamily
import all Init.Data.Range.Basic

@[expose] public section

/-!
# 06: the selected two-bit family and three unresolved exceptions

Research stage: separate the 493 successful grouped checks recorded in
`05_BatchFamilyCertificates.lean` from the three unresolved masks. The selected
family theorem requires a proof of full batch acceptance. The per-case theorem
instead requires only the shared base and that case's grouped check, avoiding
a kernel computation of the entire 493-case batch.

The fixed base has `k₀ = k₁ = 0`, `aR = 1`, and `bL = 0`. Both theorems quantify
over arbitrary third round keys and right output differences. No closed proof
of acceptance for the 493-case batch is supplied here.

The diagnostics distinguish an accepted grouped reduction with nonempty
domains from a failed grouped check, then try bounded repeated carry/grouped
passes. A contradiction found only after extra passes requires a trace
certificate; the single-step batch checker does not certify those passes.
The three exceptions remain unresolved, not proved possible.

Build and run the two diagnostics explicitly:
`lake build Magma/Evidence/06_TwoBitFamilyAndExceptions.lean`

This iteration has not been compiled or evaluated during integration. Outputs
are not recorded yet. The two `#eval` commands at the end run diagnostics only;
`profile493Batch` is available separately for a full batch verification.
Earlier research iterations are not imported or executed.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.BatchSearch Magma.BatchFamily
open Magma.FastSearch Magma.Certificates Magma.Certificates.Encoding

namespace Magma.Evidence.TwoBitFamilyAndExceptions

def exampleBase : SearchBase :=
  { k₀ := 0#32, k₁ := 0#32, aR := 1#32, bL := 0#32 }

/-! ### The three unresolved two-bit differences -/

/-- Numerically numbered from bit 0, inclusive of the low bit. -/
def unresolvedTwoBitPairs : List (Nat × Nat) :=
  [(12, 23), (13, 23), (14, 23)]

/-- These masks remain *unresolved* by our existing carry+grouped checker. -/
def unresolvedTwoBitDifferences32 : List (V 32) :=
  unresolvedTwoBitPairs.map fun (i, j) =>
    BitVec.ofNat 32 (2 ^ i + 2 ^ j)

/-- 496 two-bit masks minus the three unresolved values.
    This is a candidate family; it is a theorem only after verification. -/
def selectedTwoBitDifferences32 : List (V 32) :=
  twoBitDifferences32.filter fun aL =>
    decide (aL ∉ unresolvedTwoBitDifferences32)

/-- One shared carry base and separate grouped checks for the selected masks. -/
def example493TwoBitBatch : BatchCertificate :=
  { base := exampleBase
    proposal := proposeSearchBase exampleBase
    targets := selectedTwoBitDifferences32 }

/-! ### Pure membership lemmas (no expensive crypto evaluation) -/

private theorem twoBitDifferences32_mem
    (i j : Fin 32) (hij : i.val < j.val) :
    BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∈ twoBitDifferences32 := by
  unfold twoBitDifferences32
  apply List.mem_flatMap.mpr
  refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
  apply List.mem_map.mpr
  refine ⟨j.val, ?_, rfl⟩
  exact List.mem_filter.mpr
    ⟨List.mem_range.mpr j.isLt, (decide_eq_true_eq).mpr hij⟩

private theorem selectedTwoBitDifferences32_mem
    (i j : Fin 32) (hij : i.val < j.val)
    (hnot : BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∉
      unresolvedTwoBitDifferences32) :
    BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∈
      selectedTwoBitDifferences32 := by
  unfold selectedTwoBitDifferences32
  apply List.mem_filter.mpr
  exact ⟨twoBitDifferences32_mem i j hij,
    (decide_eq_true_eq).mpr hnot⟩

/-! ### Whole-family cryptographic soundness -/

/-- One proof of the Boolean batch check certifies every selected two-bit
    difference, uniformly in the third round key and the right output. -/
theorem twoBitFamily_impossible_of_checked
    (hchecked : verifyBatchCertificate example493TwoBitBatch = true)
    (i j : Fin 32) (hij : i.val < j.val)
    (hnot : BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∉
      unresolvedTwoBitDifferences32)
    (k₂ bR : V 32) :
    xorDDT_rounds 3
      (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val), (1#32))
      ((0#32), bR) = 0 := by
  have hm : BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∈
      example493TwoBitBatch.targets := by
    change BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val) ∈
      selectedTwoBitDifferences32
    exact selectedTwoBitDifferences32_mem i j hij hnot
  exact xorDDT_rounds_three_zero_of_verifiedBatchCertificate
    example493TwoBitBatch
    (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val))
    k₂ bR hchecked hm

/-- Alternative theorem requiring only the grouped checker for the given aL
    plus the one shared base check. This avoids a 493-case Boolean proof if
    the kernel evaluation of the entire batch is too costly. -/
theorem twoBitCase_impossible_of_checks
    (i j : Fin 32) (_hij : i.val < j.val)
    (k₂ bR : V 32)
    (hbase : verifySearchBase exampleBase
      (proposeSearchBase exampleBase) = true)
    (hgroup : verifySearchWiring
      (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val))
      (proposeSearchBase exampleBase)
      (proposeWiring (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val))
        (proposeSearchBase exampleBase)) = true) :
    xorDDT_rounds 3
      (threeRoundKeys (0#32) (0#32) k₂)
      (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val), (1#32))
      ((0#32), bR) = 0 := by
  exact xorDDT_rounds_three_zero_of_verifiedBatchHit
    exampleBase (proposeSearchBase exampleBase)
    (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val)) k₂ bR
    (proposeWiring (BitVec.ofNat 32 (2 ^ i.val + 2 ^ j.val))
      (proposeSearchBase exampleBase))
    hbase hgroup

/-! ### Diagnostics for the three unresolved differences -/

-- Runtime inputs keep proposal construction inside the measured run.
@[noinline]
private def profileThreeUnresolvedAt
    (b : SearchBase) (differences : List (V 32)) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let p := proposeSearchBase b
  let t₁ ← IO.monoMsNow
  IO.println s!"[3-exceptions] base proposal={t₁-t₀}ms"
  for aL in differences do
    let next := proposeWiring aL p
    let filtered := quickWiringContradiction aL p
    let groupedOK := verifyGroupedMaskCover aL p.carry.next next
    let empty := verifyEmptyMaskedDomain next
    IO.println s!"[3-exceptions] aL={aL.toNat}; fast={filtered}; groupedSound={groupedOK}; empty={empty}"
    IO.println s!"[3-exceptions] final Y={next.1} C={next.2}"

/-- Distinguish failure to empty a domain from rejection by the grouped checker. -/
def profileThreeUnresolved : IO Unit :=
  profileThreeUnresolvedAt exampleBase unresolvedTwoBitDifferences32

@[noinline]
private def profileThreeUnresolvedSaturationAt
    (b : SearchBase) (differences : List (V 32)) (passes : Nat) : IO Unit := do
  let p := proposeSearchBase b
  for aL in differences do
    let first := proposeWiring aL p
    let t₀ ← IO.monoMsNow
    let saturated := fastCoupledCarryWiringPropagate
      b.k₀ b.k₁ aL b.aR b.bL p.initial passes
    let t₁ ← IO.monoMsNow
    IO.println s!"[saturation] aL={aL.toNat} firstEmpty={emptyUInt16BitDomain first}; repeatedEmpty={emptyUInt16BitDomain saturated}; time={t₁-t₀}ms"
    IO.println s!"[saturation] result Y={saturated.1} C={saturated.2}"

/-- Explore bounded repeated passes; their results are not single-step certificates. -/
def profileThreeUnresolvedSaturation (passes : Nat := 16) : IO Unit :=
  profileThreeUnresolvedSaturationAt exampleBase unresolvedTwoBitDifferences32 passes

@[noinline]
private def profile493BatchAt
    (b : SearchBase) (targets : List (V 32)) (excludedCount : Nat) : IO Unit := do
  let p := proposeSearchBase b
  let t₀ ← IO.monoMsNow
  let baseOK := verifySearchBase b p
  let t₁ ← IO.monoMsNow
  let groupedOK := verifyBatchGroupedOnly p targets
  let t₂ ← IO.monoMsNow
  IO.println s!"[493] selected={targets.length}; excluded={excludedCount}"
  IO.println s!"[493] base={baseOK}; all-grouped={groupedOK}"
  IO.println s!"[493] base={t₁-t₀}ms; grouped={t₂-t₁}ms"

/-- Optionally verify the shared base once and all selected grouped witnesses. -/
def profile493Batch : IO Unit :=
  profile493BatchAt exampleBase selectedTwoBitDifferences32
    unresolvedTwoBitDifferences32.length

#eval profileThreeUnresolved

#eval profileThreeUnresolvedSaturation 16

end Magma.Evidence.TwoBitFamilyAndExceptions
