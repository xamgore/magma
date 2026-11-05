from pathlib import Path

root = Path('/Users/strebz/Documents/magma')
source = Path('/Users/strebz/Downloads/Magma_TwoBit493_FamilyAndExceptions_v1.lean').read_text()
a = source.index('/-! ### The three unresolved two-bit differences')
b = source.index('/-! ### Minimal diagnostics')
declarations = source[a:b]

header = '''import Magma.BatchFamily

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

'''

diagnostics = '''/-! ### Diagnostics for the three unresolved differences -/

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
'''

(root / 'Magma/Evidence/06_TwoBitFamilyAndExceptions.lean').write_text(
    header + declarations + diagnostics)

p = root / 'README.md'
s = p.read_text()
row = '| `05_BatchFamilyCertificates` | Can the whole one-bit family be certified, and what survives a two-bit scan? |'
assert row in s
s = s.replace(row, row + '\n| `06_TwoBitFamilyAndExceptions` | How can the selected two-bit family be certified, and why do three masks remain unresolved? |')
s = s.replace('lake build Magma/Evidence/05_BatchFamilyCertificates.lean',
              'lake build Magma/Evidence/06_TwoBitFamilyAndExceptions.lean')
p.write_text(s)
