# Magma

A Lean 4 formalization of the Magma block cipher from
[RFC 8891](https://rfc-editor.org/info/rfc8891/), with differential models, sound pruning,
independently checked certificates, and certificate search.

## Project map

The implementation of [Magma](Magma/RFC8891.lean) is the starting point. The [Difan library](Difan/README.md) develops differential laws for composing transformations; [Magma/Differential](Magma/Differential/README.md) applies them at successive round counts. Each research direction contains its Lean proofs and an `Experiments/` subdirectory with the associated notes, scripts and results. One-round DDT families are organized separately under [Magma/DDT](Magma/DDT/), with their numbered experimental iterations under [Magma/DDT/Experiments](Magma/DDT/Experiments/README.md).

For longer-round research, begin with the [five-round joins](Magma/Differential/FiveRounds/README.md), [seven-round bounds](Magma/Differential/SevenRounds/README.md), [window experiments](Magma/Differential/Windows/README.md), [nine-plus investigations](Magma/Differential/NinePlus/README.md), or [full-cipher properties](Magma/Differential/FullCipher/README.md). Each branch keeps its research notes, experimental evidence and decisions together. Git retains the dated development history; `git log --follow -- <path>` traces a relocated file.

## Working with the project

```sh
lake build
lake lean Main.lean
```

`Main.lean` is the workspace for new theorems, proofs, and interactive commands. It imports the
library through `Magma.lean`. Lake caches compiled imports; commands written directly in `Main.lean`
run on every invocation.

```sh
lake exe fmt
lake exe fmt format --diff
lake lint
lake exe axiom-audit
```

`axiom-audit` checks the compiled library against the default axiom allowlist:
`propext`, `Classical.choice`, and `Quot.sound`.

### Exporting code for LLMs

```sh
lake exe defs
python3 scripts/export_sources.py -o .lake/exports/sources.txt
```

`lake exe defs` regenerates both `.lake/exports/defs.txt` and
`.lake/exports/sources.txt`; the Python command regenerates only the source bundle
without invoking Lean.

`defs` includes definition bodies and omits proofs from the compiled library. Modules follow
dependency order; declarations follow their type and proof dependencies, with source order as the
tie-breaker. Namespace blocks shorten names and references, and leading layout whitespace is
removed. Recursive dependency components remain together. Module markers retain import names and
original file paths.

`sources.txt` contains the complete original library and magma research iterations in dependency order,
including comments and proofs. Experiments iterations follow their prerequisites and retain
their research order. The relative order of library modules matches `defs`; otherwise independent
branches follow the import order in `Magma.lean`. Source contents and indentation are preserved. The
exporter reads the iterations without compiling or executing them. Use `--library-only`
to include only the library modules. Both exports omit the aggregate `Difan.lean` and
`Magma.lean` reexport modules.
