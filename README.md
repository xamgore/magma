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
