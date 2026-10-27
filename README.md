A Lean 4 and Mathlib formalization of the Magma block cipher from
[RFC 8891](https://rfc-editor.org/info/rfc8891/), with differential models, sound pruning,
independently checked certificates, and certificate search.

```sh
lake build
lake lean Main.lean
```

`Main.lean` is the workspace for new theorems, proofs, and interactive commands. It imports the
library through `Magma.lean`. Lake caches compiled imports; commands written directly in `Main.lean`
run on every invocation.

### Library

`Magma/OneHot/` groups one-bit analysis modules. Module paths and declaration namespaces are
separate: import `Magma.OneHot.KeyClasses` and refer to declarations under `Magma.OneHotKeyClasses`.

| Module                   | Content                                                          |
|--------------------------|------------------------------------------------------------------|
| `Magma.RFC8891`          | Specification, invertibility proofs, RFC test vectors            |
| `Magma.CryptoProperties` | DDT/LAT bounds, Walsh spectra, nonlinearity                      |
| `Magma.CarryAutomaton`   | Carry model, path counts, reachability                           |
| `Magma.MultiRoundDDT`    | Feistel differentials and joint carry constraints                |
| `Magma.Pruning`          | Domain pruning, soundness, stabilization                         |
| `Magma.Certificates`     | Independent checkers and soundness, including `FastInitialCheck` |
| `Magma.FastSearch`       | Candidate generation and UInt16/UInt8 propagation                |
| `Magma.UInt8NoPathCertificates` | Independently checked no-path certificates from UInt8 proposals |
| `Magma.OneHot.CompleteSupport` | Checked positive witnesses and exact one-bit support certificates |
| `Magma.OneHot.KeyClasses` | Exact local key-class tables and conditionally certified full-word support |
| `Magma.OneHot.ClassCertificates` | Independent representative certificates and an explicit class-invariance hypothesis |
| `Magma.OneHot.CarryPrefix` | Universal prefix-carry classification and preservation under key-class representatives |
| `Magma.OneHot.SilentNibbleStructure` | Silent-nibble carry structure, active-nibble nonzero output, and the original local-step bridge |
| `Magma.OneHot.BoundaryReduction` | Exact prefix/active/suffix boundary reduction and invariance across key classes |
| `Magma.OneHot.TraceSplit5` | Exact 5+1+2 trace split and the actual DDT criterion through prefix and active-step witnesses |
| `Magma.OneHot.PrefixArithmeticBridge` | Arithmetic semantics of the trace prefix and unconditional full-word DDT support at bits 20–23 |
| `Magma.OneHot.FullKeyClassInvariant` | Unconditional one-bit DDT support classification and key-class invariance for every key |
| `Magma.OneHot.ThreeRoundColumns` | Universal zero-left three-round one-bit column support and the unique class with all columns zero |
| `Magma.OneHot.ExactColumnMass` | Exact carry-DP column masses and unequal multiplicities within one support class |
| `Magma.OneHot.LinearPrefixMass` | Symbolic prefix-carry counts and an affine factorized model, with conditional DDT consequences |
| `Magma.OneHot.QuantitativeTraceFactorization` | Symbolic 5+1+2 trace counting and unconditional affine DDT and column-mass formulae |
| `Magma.OneHot.ExactCoefficientMasks` | Exact local coefficient masks, closed DDT and column masses, and four affine regimes |
| `Magma.OneHot.GlobalMaximum` | Sharp maxima for the one-bit DDT slice and three-round column masses, with all attaining key classes |
| `Magma.OneHot.FixedKeyPeak` | Exact peak and an attaining bit for each key, with arithmetic counts of maximizing classes |
| `Magma.OneHot.ActualKeyCardinality` | Exact cardinalities of the actual 32-bit keys attaining and missing the one-bit DDT maximum |
| `Magma.BatchSearch`      | Shared carry bases and independently checked batch hits          |
| `Magma.BatchFamily`      | Batch certificates, family soundness, and two-bit candidates     |

### Research iterations

`Magma/Evidence/` records research iterations in order, outside the default build. Each file states
its question, preserves experiments and historical observations, and explains what motivated the
next iteration.

| Iteration                      | Research question                                                                               |
|--------------------------------|-------------------------------------------------------------------------------------------------|
| `01_UInt16Search`              | Can local deletion find a certificate, and where does search spend time?                        |
| `02_CarryGroupedPropagation`   | Do whole carry paths and grouped wiring expose a contradiction?                                 |
| `03_FastInitialCover`          | Can the concrete impossibility proof reuse a faster sound coverage check?                       |
| `04_BatchCarryGroupedSearch`   | Can one verified carry base serve many left input differences?                                  |
| `05_BatchFamilyCertificates`   | Can the whole one-bit family be certified, and what survives a two-bit scan?                    |
| `06_TwoBitFamilyAndExceptions` | How can the selected two-bit family be certified, and why do three masks remain unresolved?     |
| `07_ThreeExceptionalWitnesses` | Do explicit inputs give positive DDT support for the three exceptional masks?                   |
| `08_ZeroLeftSupport`           | Do two exact S-box tables explain 64 predicted pairs and the three two-bit exceptions?          |
| `09_ZeroLeftExactDDT`          | Can sixteen exact S-box factors determine the three exceptional DDT counts for every third key? |
| `10_ZeroLeft64ExactCounts`     | Do all 64 predicted pairs have the same exact DDT count for every third key?                    |
| `11_ZeroLeft64Completeness`    | Does conservation of DDT mass prove that the 64-pair list is complete?                          |
| `12_ZeroLeftArbitraryKeys`     | Which one-bit output columns vanish for arbitrary keys, is total mass preserved, and can UInt8 scan them quickly? |
| `13_UInt8NoPathCertificates`  | Can original carry arithmetic independently certify the UInt8 scan's one-bit exclusions?       |
| `14_OneHotCompleteSupport`   | Do checked positive witnesses and no-path certificates give exact one-bit support for three keys? |
| `15_OneHotKeyClasses`        | Do 32 local key classes agree with UInt8 scans, and which class predicts empty one-bit support? |
| `16_OneHotClassCertificates` | Do original-arithmetic certificates establish exact support for all 32 class representatives? |
| `17_OneHotExactColumnMass` | Do keys with the same one-bit support class also have equal exact column masses? |

Fixed observations are Lean examples and theorems. Measurements use `#eval`. Run an iteration
explicitly; iterations import the library directly and do not run earlier experiments:

```sh
lake build Magma/Evidence/01_UInt16Search.lean
```

### Formatting

```sh
lake exe fmt
lake exe fmt format --diff
lake lint
```

### Inspection

```sh
lake exe defs > .lake/defs.txt
lake exe deps > .lake/deps.json
lake exe axiom-audit
```

`defs` includes definition bodies and omits proofs. The dependency JSON format is documented in the
module comment in `Dependencies.lean`.

`axiom-audit` checks the compiled library against the default axiom allowlist:
`propext`, `Classical.choice`, and `Quot.sound`.
