# Sparse adjacent classes and 5+round window research

**Status (2026-11-03):** a kernel-checked *sound* n-round key-free
difference transducer is now in
`Magma/Diffan/KeyFreeRoundTransducer.lean` (commit `588179c`).
The current scanner below is for **five ordinary Feistel rounds only**.
The general n-round Lean theorem is not a claim that the SAT executable
already supports 6+ rounds.

## What is proved

For any actual single-round difference
`(aL,aR) -> (bL,bR)`, we must have `bL=aR`, and the
previously verified local carry automaton must accept
`aR -> bR XOR aL`. This holds with both halves active and arbitrary
round keys.

`Path n a b` composes these **necessary** one-round relations.
`path_of_actual_delta` shows every actual n-round trajectory induces
such a path, and `ddt_zero_of_no_keyFreePath` rules out a real DDT
coefficient whenever the relaxed path set is empty. `Path.split` and
`ddt_zero_of_no_five_window_cut` give a formally sound
`m + 5 + r` decomposition at two arbitrary cut boundaries.

**No independence claim:** intermediate real base states and the
single RFC 8891 master key are correlated. The transducer forgets them
and therefore can have false positives. In particular, a five-round
outer zero does **not** automatically imply a zero of a longer
cipher: one must show that every compatible internal five-round cut
lands in the forbidden class.

## Repeatable five-round exploratory scanner

The new standalone Rust program `research/adjacent_scan.rs` generates
two reproducible, deduplicated sets of **full 64-bit differences**, with
independent weights for their left/right halves; it optionally calls
the existing `magma_exact_matrix_corrected_v3.rs` with
`--family general --mode universal`. It does not duplicate or
silently modify the SAT encoding. A positive SAT model is checked
against five real rounds by that existing scanner; UNSAT still relies
on the solver/CNF correctness and has **no Lean certificate**.

From the project root:

```bash
rustc --edition=2021 -O research/adjacent_scan.rs -o /tmp/magma-adjacent-scan

/tmp/magma-adjacent-scan \
  --input-weights 1,1 --output-weights 1,1 \
  --inputs 48 --outputs 48 --seed 20261103 \
  --window-start 0 --threads 6 --timeout-ms 5000 \
  --out research/adjacent_runs/both11_test --run
```

`--input-weights L,R` and `--output-weights L,R` refer to
Hamming weights of the two 32-bit halves, not total 64-bit weight.
Examples to try independently: `1,1 -> 1,0`, `1,0 -> 1,1`,
`0,1 -> 1,1`, `1,1 -> 2,0`, and `1,1 -> 0,2`.
For a different ordinary five-round schedule window use
`--window-start 1` through `26`.
`--max-cells N` allows a bounded first pass. Use unique output
directories: the tool refuses to overwrite an existing directory.
For `--run`, the default existing SAT scanner path is
`~/Downloads/P8_matrix_analysis_2026-11-02/magma_exact_matrix_corrected_v3.rs`;
override with `--scanner PATH`.

Results include `inputs.txt`, `outputs.txt`, `CONFIG.txt`,
and (if `--run`) the original runner's `run/meta.json`, zstd
matrix and SAT witnesses. Output directories are intentionally
ignored by Git; the Rust source and this note can be committed.

## Where deeper investigation may pay off

1. A transducer for **five consecutive rounds as one certified
   macro-edge**, retaining compatible middle-state/carry correlations.
   Replace the weak `Path 5` relation in a cut with this macro-edge
   and prove its soundness. This is the promising bridge from the
   existing sharp outer weight-sum candidate `B5=5` to long windows.
2. Test whether a six- or seven-round prefix/suffix can **force
   internal cuts** into `(a,0) -> (0,s)`; otherwise the outer bound
   cannot be transferred merely by multiplying or concatenating DDTs.
3. For 6+ exact SAT experiments a **separate variable-round CNF
   encoding and independent trajectory replayer** are required.
   Do not label a five-round SAT result as a seven-round result.
4. The `NibblePairCertificates.lean` draft currently fails the strict
   axiom audit because of native `bv_decide` axioms. Do not use that
   module to claim kernel-certified impossibility until fixed.

This note deliberately distinguishes confirmed Lean soundness,
computational SAT evidence, and conjectured improvements.

## Measured adjacent-class probe (2026-11-03)

The command above was actually run with `--inputs 48 --outputs 48`,
both halves of every input/output difference of weight 1,
`--window-start 0 --threads 6`, symbolic master key.

- Completed: **2,304/2,304** cells, **1,086 SAT**, **1,218 UNSAT**,
  **zero timeouts/errors**, 149.69 s SAT runtime.
- All **1,086 SAT** base-state/master-key witnesses independently
  recomputed by `python3 research/verify_adjacent.py`; compressed
  matrix SHA-256 matched its metadata.
- Input/output word `0x0000000100080000` is one verified positive
  diagonal of the *general* 64-bit difference relation.
  Its two halves have exactly one active bit each.
- `Magma/Diffan/AdjacentPositiveExample.lean` kernel-checks that
  concrete diagonal five-round trajectory and its positive DDT,
  without trusting SAT.

The contrast is sharp: the five-round weight-sum threshold candidate
`B5=5` applies to the special **outer** family
`(alpha,0) -> (0,sigma)`; for two active halves there are reachable
total-weight-2 input/output differences. The sharp outer property is
**not** an automatic generic Feistel branch-number bound.

For the exact run artefacts:
`research/adjacent_runs/weight11_to_weight11/run/`.
They are ignored by Git; `independent_verification.json` records
the SHA check and the witness replay count.

Key-schedule caution: the default outer experiments start at round 0.
Five-round windows crossing the RFC 8891 forward-to-reverse scheduling
boundary can repeat a master-key word *within* a window
(starts 20, 21, 22, 23). Such windows have stricter constraints than
five completely independent round keys. The wrapper exposes
`--window-start` so those can be examined separately.

## Schedule-boundary pilot (same first 256 cells)

The same 48x48 grids were rechecked in the five-round window
starting at round 21, where the RFC 8891 subkey indices are
`[5,6,7,7,6]` rather than five independent master words.
Only the **first 256/2304 cells** were scheduled, in a separate
directory `research/adjacent_runs/boundary21_first256/`.

- Start 0 on those exact 256 cells: **132 SAT, 124 UNSAT**.
- Start 21 on those same 256: **124 SAT, 124 UNSAT,
  8 TIMEOUT, 2048 NOT_RUN** in the full 48x48 matrix.
- All 124 positive start-21 witnesses were independently recomputed.
  SHA-256 and matrix histograms were also checked.
- Cross-tab: 124 SAT->SAT, 124 UNSAT->UNSAT, **8 SAT->TIMEOUT**.
  No SAT->UNSAT was established by this pilot.

The schedule correlation may reduce reachable support, but these
eight timeouts are **unknown**, not exclusions. Do not extrapolate
this 256-cell comparison to the entire class.
