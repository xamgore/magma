from pathlib import Path

root = Path('/Users/strebz/Documents/magma')
source = Path('/Users/strebz/Downloads/Magma_BatchFamilyCertificates_v1.lean').read_text()

def section(start, end):
    return source[source.index(start):source.index(end)]

generic = section('/-! ### 1.', '/-! ### 2.')
exploration = section('/-! ### 3.', '/-! ### 4.')
library = '''import Magma.BatchSearch

/-!
# Certificates for families of three-round impossible XOR differentials

`BatchCertificate` shares one independently checked initial/carry base across
its target differences. Every target's grouped witness is checked separately.
Acceptance establishes zero three-round DDT for every member, for arbitrary
third keys and right output differences.

The two-bit candidate generator and fast prefilter do not assert impossibility.
`independentlyVerifiedHits` checks each retained grouped witness; its soundness
theorem additionally requires acceptance of the shared base.
Concrete one-bit family proofs and exploratory two-bit runs are recorded in
`Magma/Evidence/05_BatchFamilyCertificates.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.BatchSearch

namespace Magma.BatchFamily

'''
library += generic + exploration + 'end Magma.BatchFamily\n'
(root / 'Magma/BatchFamily.lean').write_text(library)

# The one-bit generator is now reused by two research iterations.
p = root / 'Magma/Evidence/04_BatchCarryGroupedSearch.lean'
s = p.read_text()
a = s.index('/-- 32 independent one-bit differences;')
b = s.index('def exampleBase', a)
one_bit = s[a:b]
p.write_text(s[:a] + s[b:])
p = root / 'Magma/BatchSearch.lean'
s = p.read_text().replace('end Magma.BatchSearch', one_bit + 'end Magma.BatchSearch')
p.write_text(s)

family = section('/-! ### 2.', '/-! ### 3.')
evidence = '''import Magma.BatchFamily

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

'''
evidence += family
evidence += '''/-! ### Diagnostics: grouped costs versus the shared base -/

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
  match checked.head? with
  | some aL => IO.println s!"[two-bit] first verified aL={aL.toNat}"
  | none => IO.println "[two-bit] no independently verified hit"

/-- Check every one-bit grouped witness without repeating the shared base check. -/
def profileAllOneBitGrouped : IO Unit :=
  profileAllOneBitGroupedAt exampleBase oneBitDifferences32

/-- Check the shared base once, then all 32 grouped witnesses. -/
def profileFullOneBitBatch : IO Unit :=
  profileFullOneBitBatchAt exampleOneBitBatch

/-- Explore all two-bit differences and independently check each prefiltered hit. -/
def profileTwoBitFamily : IO Unit :=
  profileTwoBitFamilyAt exampleBase twoBitDifferences32

#eval profileAllOneBitGrouped

#eval profileFullOneBitBatch

#eval profileTwoBitFamily

end Magma.Evidence.BatchFamilyCertificates
'''
(root / 'Magma/Evidence/05_BatchFamilyCertificates.lean').write_text(evidence)

p = root / 'Magma.lean'
s = p.read_text().replace('import Magma.BatchSearch\n', 'import Magma.BatchSearch\nimport Magma.BatchFamily\n', 1)
p.write_text(s)
p = root / 'README.md'
s = p.read_text().replace('| `Magma.BatchSearch`      | Shared carry bases and independently checked batch hits          |', '| `Magma.BatchSearch`      | Shared carry bases and independently checked batch hits          |\n| `Magma.BatchFamily`      | Batch certificates, family soundness, and two-bit candidates      |')
s = s.replace('| `04_BatchCarryGroupedSearch` | Can one verified carry base serve many left input differences? |', '| `04_BatchCarryGroupedSearch` | Can one verified carry base serve many left input differences? |\n| `05_BatchFamilyCertificates` | Can the whole one-bit family be certified, and what survives a two-bit scan? |')
s = s.replace('lake build Magma/Evidence/04_BatchCarryGroupedSearch.lean', 'lake build Magma/Evidence/05_BatchFamilyCertificates.lean')
p.write_text(s)
