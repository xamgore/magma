# Magma

A Lean 4 and Mathlib formalization of the Magma block cipher from
[RFC 8891](https://rfc-editor.org/info/rfc8891/), with differential models, sound pruning,
independently checked certificates, and certificate search.

## Project map

The implementation of [Magma](Magma/RFC8891.lean) is the starting point. The [Diffan library](Diffan/README.md) develops differential laws for composing transformations; [Magma/Differential](Magma/Differential/README.md) applies them at successive round counts. Each research direction contains its Lean proofs and an `Experiments/` subdirectory with the associated notes, scripts and results. One-round DDT families are organized separately under [Magma/DDT](Magma/DDT/), with their numbered experimental iterations under [Magma/DDT/Experiments/Evidence](Magma/DDT/Experiments/Evidence).

For longer-round research, begin with the [five-round joins](Magma/Differential/FiveRounds/README.md), [seven-round bounds](Magma/Differential/SevenRounds/README.md), [window experiments](Magma/Differential/Windows/README.md), [nine-plus investigations](Magma/Differential/NinePlus/README.md), or [full-cipher properties](Magma/Differential/FullCipher/README.md). Each branch keeps its research notes, experimental evidence and decisions together. Git retains the dated development history; `git log --follow -- <path>` traces a relocated file.

## Working with the project

```sh
lake build
lake lean Main.lean
```

`Main.lean` is the workspace for new theorems, proofs, and interactive commands. It imports the
library through `Magma.lean`. Lake caches compiled imports; commands written directly in `Main.lean`
run on every invocation.

### Research iterations

`Magma/DDT/Experiments/Evidence/` records research iterations in order, outside the default build. Each file states
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
| `19_DiagonalExactWeights` | Do the proposed diagonal weights agree numerically with the carry DP at the zero key and the 72-cell witness key? |
| `20_TwoHotOutputOneExactCounts` | What fixed values does the proposed weighted formula give at the zero key and the cross-nibble witness key? |
| `21_TwoHotOutputOneDPAgreement` | Does a fast four-state scan agree with the proposed weighted formula on all seven pairs at eight sample keys? |

Fixed observations are Lean examples and theorems. Measurements use `#eval`. Run an iteration
explicitly; iterations import the library directly and do not run earlier experiments:

```sh
lake build Magma/DDT/Experiments/Evidence/01_UInt16Search.lean
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
