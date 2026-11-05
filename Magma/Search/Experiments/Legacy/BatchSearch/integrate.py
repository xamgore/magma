from pathlib import Path

root = Path('/Users/strebz/Documents/magma')
source = Path('/Users/strebz/Downloads/Magma_BatchCarryGroupedSearch_v1.lean').read_text()
a = source.index('/-! ## Fixed base:')
b = source.index('/-! ## One-bit candidates')
library = '''import Magma.FastSearch

/-!
# Batch search for three-round impossible XOR differentials

For fixed `(k₀, k₁, aR, bL)`, initial domains and carry propagation are shared
across candidate left input differences `aL`. Search proposals and the fast
grouped prefilter are untrusted. An accepted shared base and an independently
accepted grouped witness imply zero three-round DDT for arbitrary `k₂` and `bR`.

`firstVerifiedAL` checks grouped witnesses only. Full cryptographic soundness
also requires `verifySearchBase`; the zero-DDT theorems require both checks.
Experiment inputs, measurements, and recorded outcomes are in
`Magma/Evidence/04_BatchCarryGroupedSearch.lean`.
-/

open Magma.Internal Magma.MultiRoundDDT Magma.Certificates
open Magma.Certificates.Encoding Magma.Certificates.BackwardMask
open Magma.Certificates.FastInitialCheck Magma.FastSearch

namespace Magma.BatchSearch

'''
library += source[a:b] + 'end Magma.BatchSearch\n'
(root / 'Magma/BatchSearch.lean').write_text(library)

evidence = '''import Magma.BatchSearch

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

'''
c = source.index('/-- 32 independent one-bit differences;')
d = source.index('/-\n  Test in this order:', c)
evidence += source[c:d]
evidence += '''-- Measurements remain evaluations; shared and per-hit acceptance are distinct.
#eval profileBatchSearch

#eval profileBatchBaseVerification

#eval profileBatchFirstVerifiedHit

end Magma.Evidence.BatchCarryGroupedSearch
'''
(root / 'Magma/Evidence/04_BatchCarryGroupedSearch.lean').write_text(evidence)

p = root / 'Magma.lean'
s = p.read_text().replace('import Magma.FastSearch\n', 'import Magma.FastSearch\nimport Magma.BatchSearch\n', 1)
p.write_text(s)

p = root / 'README.md'
s = p.read_text().replace('| `Magma.FastSearch`       | Candidate generation and UInt16/UInt8 propagation                |', '| `Magma.FastSearch`       | Candidate generation and UInt16/UInt8 propagation                |\n| `Magma.BatchSearch`      | Shared carry bases and independently checked batch hits          |')
s = s.replace('| `03_FastInitialCover` | Can the concrete impossibility proof reuse a faster sound coverage check? |', '| `03_FastInitialCover` | Can the concrete impossibility proof reuse a faster sound coverage check? |\n| `04_BatchCarryGroupedSearch` | Can one verified carry base serve many left input differences? |')
s = s.replace('lake build Magma/Evidence/03_FastInitialCover.lean', 'lake build Magma/Evidence/04_BatchCarryGroupedSearch.lean')
s = s.replace('its accelerated initial-coverage check.', 'its accelerated initial-coverage check, followed by batch search with a shared base.')
p.write_text(s)
