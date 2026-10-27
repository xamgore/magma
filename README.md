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
separate: import `OneHot.KeyClasses` and refer to declarations under `OneHotKeyClasses`.

`Magma/ZeroLeft/` groups the later work on column transport and exact coefficients. It imports
earlier zero-left results from `MultiRoundDDT` and one-bit results from
`Magma/OneHot/`. The support and completeness proofs behind iterations 08, 10, and 11 belong to
`MultiRoundDDT`.
`UnitInputParity` proves the general row invariant independently;
`ZeroLeft.KeyParity` combines it with the eight-offset classification.
`OddUnitInput77` gives the complete 77-entry odd-key reference row, and
`ZeroLeft.OddKey` applies its exact counts to three-round columns.
`ZeroLeft.ParityCompleteSlice` unifies both parities into exact coefficients, supports, and column
cardinalities of zero, eight, or 77 for arbitrary round keys with right input difference one and
left output difference zero.

| Module                                  | Content                                                                                                                                    |
|-----------------------------------------|--------------------------------------------------------------------------------------------------------------------------------------------|
| `RFC8891`                               | Specification, invertibility proofs, RFC test vectors                                                                                      |
| `CryptoProperties`                      | DDT/LAT bounds, Walsh spectra, nonlinearity                                                                                                |
| `CarryAutomaton`                        | Carry model, path counts, reachability                                                                                                     |
| `UnitInputParity`                       | The entire unit-input DDT row depends only on key parity, by even-translation invariance                                                   |
| `OddUnitInput77`                        | Kernel-certified 77-entry unit-input DDT row for every odd key, complete by conserved mass                                                 |
| `MultiRoundDDT`                         | Feistel differentials, joint carry constraints, and the complete 64-pair zero-key slice                                                    |
| `Pruning`                               | Domain pruning, soundness, stabilization                                                                                                   |
| `Certificates`                          | Independent checkers and soundness, including `FastInitialCheck`                                                                           |
| `FastSearch`                            | Candidate generation and UInt16/UInt8 propagation                                                                                          |
| `UInt8NoPathCertificates`               | Independently checked no-path certificates from UInt8 proposals                                                                            |
| `OneHot.CompleteSupport`                | Checked positive witnesses and exact one-bit support certificates                                                                          |
| `OneHot.KeyClasses`                     | Exact local key-class tables and conditionally certified full-word support                                                                 |
| `OneHot.ClassCertificates`              | Independent representative certificates and an explicit class-invariance hypothesis                                                        |
| `OneHot.CarryPrefix`                    | Universal prefix-carry classification and preservation under key-class representatives                                                     |
| `OneHot.SilentNibbleStructure`          | Silent-nibble carry structure, active-nibble nonzero output, and the original local-step bridge                                            |
| `OneHot.BoundaryReduction`              | Exact prefix/active/suffix boundary reduction and invariance across key classes                                                            |
| `OneHot.TraceSplit5`                    | Exact 5+1+2 trace split and the actual DDT criterion through prefix and active-step witnesses                                              |
| `OneHot.PrefixArithmeticBridge`         | Arithmetic semantics of the trace prefix and unconditional full-word DDT support at bits 20–23                                             |
| `OneHot.FullKeyClassInvariant`          | Unconditional one-bit DDT support classification and key-class invariance for every key                                                    |
| `OneHot.ThreeRoundColumns`              | Universal zero-left three-round one-bit column support and the unique class with all columns zero                                          |
| `OneHot.ExactColumnMass`                | Exact carry-DP column masses and unequal multiplicities within one support class                                                           |
| `OneHot.LinearPrefixMass`               | Symbolic prefix-carry counts and an affine factorized model, with conditional DDT consequences                                             |
| `OneHot.QuantitativeTraceFactorization` | Symbolic 5+1+2 trace counting and unconditional affine DDT and column-mass formulae                                                        |
| `OneHot.ExactCoefficientMasks`          | Exact local coefficient masks, closed DDT and column masses, and four affine regimes                                                       |
| `OneHot.GlobalMaximum`                  | Sharp maxima for the one-bit DDT slice and three-round column masses, with all attaining key classes                                       |
| `OneHot.FixedKeyPeak`                   | Exact peak and an attaining bit for each key, with arithmetic counts of maximizing classes                                                 |
| `OneHot.ActualKeyCardinality`           | Exact cardinalities of the actual 32-bit keys attaining and missing the one-bit DDT maximum                                                |
| `OneHot.CompletePeakHistogram`          | Exact histogram of fixed-key one-bit DDT peaks across all 32-bit round keys                                                                |
| `OneHot.MaximizingBitMultiplicity`      | Counts of maximizing one-bit positions at each key and their exact distribution over actual keys                                           |
| `OneHot.JointPeakMultiplicity`          | Joint peak and maximizing-position fibers over actual keys, with exact counts for the two extreme cells                                    |
| `OneHot.JointPeakMultiplicityHistogram` | Complete joint histogram of one-bit DDT peaks and maximizing-position counts over all round keys                                           |
| `OneHot.UniversalLowerNibbleZeros`      | Symbolic lower-nibble exclusion for arbitrary differences and 448 universally zero cells in the full one-hot DDT matrix                    |
| `OneHot.ActiveNibbleNecessary`          | First-active-nibble necessity for arbitrary differences, 896 zero off-diagonal one-hot cells, and at most 128 positive cells for every key |
| `OneHot.DiagonalCarryMasks`             | Certified local S-box/carry masks, 948 universally zero one-hot cells, and at most 76 positive cells for every key                         |
| `OneHot.CandidateSharpWitnesses`        | Explicit RFC witnesses for all 76 candidates; exact one-hot support over the union of keys and 948 universally impossible cells            |
| `OneHot.FixedKeySupportAudit`           | Exact carry-DP support for any fixed key, certified 72-cell support at `0x06120010`, and a separate 72-cell local-model ceiling            |
| `OneHot.Support72KeyClasses` | Exact nibble conditions for attaining 72 cells, fourteen admissible prefixes, and 2016 maximizing coordinate tuples |
| `OneHot.Support72ActualKeyCardinality` | Exactly 2016 actual 32-bit round keys attain the 72-cell support maximum, via the word-to-nibble equivalence |
| `OneHot.SupportHistogramDP` | Certified two-state DP table for support weights and cardinality reindexing to nibble fibers; identifying the DP coefficients with these fibers remains open |
| `ZeroLeft.ColumnTransport`              | Exact coefficient transport, translated supports, and cross-column proportionality for arbitrary keys                                      |
| `ZeroLeft.EightEntries`                 | Eight equal positive entries per nonempty column with first key zero, and exact affine values for one-bit outputs                          |
| `ZeroLeft.KeyParity`                    | First-key parity reduction of the zero-left slice and eight equal entries for every even first key                                         |
| `ZeroLeft.OddKey`                       | Exact three-round zero-left coefficients for odd first keys and arbitrary second and third keys                                            |
| `ZeroLeft.ParityCompleteSlice`          | Unified exact coefficients and supports for both first-key parities, with column cardinalities 0, 8, or 77                                 |
| `ZeroLeft.IndividualCoefficientMaxima`  | Attained maxima of individual column coefficients and sharp parity-sensitive bounds for one-bit right outputs                              |
| `BatchSearch`                           | Shared carry bases and independently checked batch hits                                                                                    |
| `BatchFamily`                           | Batch certificates, family soundness, and two-bit candidates                                                                               |

### Research iterations

`Magma/Evidence/` records research iterations in order, outside the default build. Each file states
its question, preserves experiments and historical observations, and explains what motivated the
next iteration.

| Iteration                      | Research question                                                                                                        |
|--------------------------------|--------------------------------------------------------------------------------------------------------------------------|
| `01_UInt16Search`              | Can local deletion find a certificate, and where does search spend time?                                                 |
| `02_CarryGroupedPropagation`   | Do whole carry paths and grouped wiring expose a contradiction?                                                          |
| `03_FastInitialCover`          | Can the concrete impossibility proof reuse a faster sound coverage check?                                                |
| `04_BatchCarryGroupedSearch`   | Can one verified carry base serve many left input differences?                                                           |
| `05_BatchFamilyCertificates`   | Can the whole one-bit family be certified, and what survives a two-bit scan?                                             |
| `06_TwoBitFamilyAndExceptions` | How can the selected two-bit family be certified, and why do three masks remain unresolved?                              |
| `07_ThreeExceptionalWitnesses` | Do explicit inputs give positive DDT support for the three exceptional masks?                                            |
| `08_ZeroLeftSupport`           | Do two exact S-box tables explain 64 predicted pairs and the three two-bit exceptions?                                   |
| `09_ZeroLeftExactDDT`          | Can sixteen exact S-box factors determine the three exceptional DDT counts for every third key?                          |
| `10_ZeroLeft64ExactCounts`     | Do all 64 predicted pairs have the same exact DDT count for every third key?                                             |
| `11_ZeroLeft64Completeness`    | Does conservation of DDT mass prove that the 64-pair list is complete?                                                   |
| `12_ZeroLeftArbitraryKeys`     | Which one-bit output columns vanish for arbitrary keys, is total mass preserved, and can UInt8 scan them quickly?        |
| `13_UInt8NoPathCertificates`   | Can original carry arithmetic independently certify the UInt8 scan's one-bit exclusions?                                 |
| `14_OneHotCompleteSupport`     | Do checked positive witnesses and no-path certificates give exact one-bit support for three keys?                        |
| `15_OneHotKeyClasses`          | Do 32 local key classes agree with UInt8 scans, and which class predicts empty one-bit support?                          |
| `16_OneHotClassCertificates`   | Do original-arithmetic certificates establish exact support for all 32 class representatives?                            |
| `17_OneHotExactColumnMass`     | Do keys with the same one-bit support class also have equal exact column masses?                                         |
| `18_OneHotFixedKeySupport`     | How many of the 76 globally realizable cells coexist at one key, and what ceiling follows from consistent local carries? |

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
python3 scripts/export_sources.py -o .lake/sources.txt --mermaid .lake/modules.mmd
python3 scripts/theorem_graph.py -o .lake/theorems.mmd
lake exe axiom-audit
```

`defs` includes definition bodies and omits proofs from the compiled library. Modules follow
dependency order; declarations follow their type and proof dependencies, with source order as the
tie-breaker. Namespace blocks shorten names and references, and leading layout whitespace is
removed. Recursive dependency components remain together. Module markers retain import names and
original file paths.

`sources.txt` contains the complete original library and Evidence sources in dependency order,
including comments and proofs. Numbered Evidence iterations follow their prerequisites and retain
their research order. The relative order of library modules matches `defs`; otherwise independent
branches follow the import order in `Magma.lean`. Source contents and indentation are preserved. The
exporter reads Evidence without compiling or executing its experiments. Use `--library-only`
for just the compiled library. Downloads are not needed to regenerate either export. Both reading
exports and the diagram omit the aggregate `Magma.lean` reexport module.

`axiom-audit` checks the compiled library against the default axiom allowlist:
`propext`, `Classical.choice`, and `Quot.sound`.
