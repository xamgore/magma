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

## 2026-11-03: correlated five-round macro for arbitrary-length windows

Lean module: Magma/Diffan/CorrelatedFiveMacro.lean.

The earlier key-free Path n graph forgets 64-bit base states. The new
Correlated n predicate carries the exact base and XOR difference
through each round; it supports splitting at any m+n boundary and
reification as a genuine sequence of Magma rounds.

For outer transitions (a,0) -> (0,s), a key-independent *exact*
existence relation has been proved:

  OuterCoupled a s :=
    exists k1 k2 k3 R Z,
      threeRoundCoupled k1 k2 k3 0 a s 0 R Z.

  universal_outer_zero_iff_no_coupled:
    (forall five independently chosen k0..k4,
      DDT5[k0..k4] ((a,0),(0,s)) = 0)
    iff NOT OuterCoupled a s.

This equivalence is Lean-proved. It is *not* a Markov approximation
or a product of independent DDT counts: R, Z and the three middle
round constraints remain correlated. OuterCoupled is also symmetric
under reversing five round keys.

The refined Macro5 checks the existing key-free five-edge relation,
certified outer structural obstructions, and the exact existential
three-round core whenever the cut has the outer shape. Its soundness
follows from Correlated.reify. Theorems for six and seven rounds
(sixRound_zero_of_no_one_five and sevenRound_zero_of_no_one_five_one)
and for arbitrary m+5+r use this refined middle condition without
assuming independent actual round keys or base states.

Limits and research target:
- OuterCoupled is a mathematical EXISTS predicate, not yet a fast
  executable kernel-certified SAT-free decision procedure. Derive an
  eight-nibble joint carry transducer retaining the R/Z constraints,
  and prove it sound (ideally complete on the outer slice).
- The macro only adds the exact outer-core condition when the five-
  round cut has zero right-input and zero left-output difference.
  Work out which six-/seven-round boundary patterns FORCE such a cut.
- For a window with repeated RFC 8891 master-key words,
  universal impossibility over five independent keys remains sound,
  but the converse may fail due to schedule restrictions.
- The refined relation is contained in the earlier key-free Path
  graph. No *strict* separation example between the two relations has
  yet been proved; measure this before claiming a quantitative gain.

## 2026-11-03: exact 5..32 round SAT runner + verified 6/7 core reduction

The new `research/magma_exact_matrix_nround.rs` is a separate,
parameterized fork of the corrected v3 solver, not a modification of the
original file under Downloads. Use `--rounds N` (5..32) and
`--window-start S` with S+N <= 32; all are **ordinary** Feistel rounds
(the RFC terminal G* convention is not silently substituted).
`--mode universal` uses ONE symbolic 256-bit master key with the real
RFC 8891 schedule. Each SAT model is rechecked with exactly N real
rounds. Every UNSAT conclusion remains dependent on the CNF and solver,
not Lean/kernel certification.

Lean module `Magma/Diffan/SixSevenOuterReduction.lean` specializes
the already proved `twoSided_boundary_ddt_eq_inner` exactly:
`D6((a,0),(0,s)) = D4_inner((0,a),(s,0))`,
`D7((a,0),(0,s)) = D5_inner((0,a),(s,0))`.
The first and last subkeys do not affect these coefficients if inner
round keys are held fixed (even when some words are repeated).
The SAT runner therefore by default strips both boundary rounds for
outer pairs when N>5, returning the same full-N status, and reconstructs
the original base state by undoing the first actual round.
`--no-outer-reduction` forces the full CNF, for A/B verification.
For N=5 the original verified three-round special core is retained.

**Observed verified first trials (same cell sets, start=0):**

| Family / cells processed | N=5 SAT/UNSAT | N=6 SAT/UNSAT | N=7 SAT/UNSAT |
|---|---:|---:|---:|
| General (both halves active), first 16 cells of 8x8 | 5/11 | 14/2 | 16/0 |
| Outer (1-hot input to 2-hot output), all 16 cells of 4x4 | 0/16 | 1/15 | 10/6 |

No unknowns/errors in those completed cells. The N=5 general status
matrix matched the old corrected v3 runner byte-for-byte. For the N=6
and N=7 outer 4x4 matrices, new reduced CNF, explicit
`--no-outer-reduction` full CNF and pre-optimization baseline all
matched **exactly** cell-by-cell, including solver UNSAT statuses.
All positive witnesses across these runs were independently replayed
with the separate `research/verify_nround.py` implementation.

**Measured SAT solving time for the outer 4x4 sample (6 threads):**
N=6 full 1.1 s, reduced 0.4 s; N=7 full 3.4 s, reduced 1.7 s.
Small-sample timing only; not a general speedup bound.

Two positive transitions with exactly the same external differences
`(0x00000001,0) -> (0,0x00000021)` have additionally been **proved
in Lean**, for both 6 and 7 rounds, with explicit valid 256-bit RFC
master-key schedules:
`Magma/Diffan/SixSevenRoundOuterPositive.lean`, theorems
`sixRound_master_positive` and `sevenRound_master_positive`.
The N=5 UNSAT cell for this particular pair is NOT yet Lean-proved:
its first active input/output nibbles coincide, so the existing
different-nibble theorem does not apply.

A reproducible example, from the repository root:

```bash
./research/magma_exact_matrix_nround.rs -- \
  --rounds 7 --family outer \
  --input-file research/nround_fixtures/outer_4_inputs.txt \
  --output-file research/nround_fixtures/outer_4_outputs.txt \
  --mode universal --solver cadical --threads 6 --timeout-ms 5000 \
  --max-cells 0 --out research/nround_runs/my_new_7_round_probe
python3 research/verify_nround.py research/nround_runs/my_new_7_round_probe
```

Each run directory retains its compressed matrix, metadata, witnesses,
SHA256 checks and independent verification JSON. Different N and
reduction modes use separate output directories. Run `--self-test`
with N=5 to exercise RFC vectors and CNF. The full solver self-test at
N=6 exceeded its 12s per-cell SAT limit; this is an unresolved
**timeout**, not evidence for a wrong encoding. Actual N=6/7 SAT
witnesses have been exhaustively independently replayed on the test
matrices.

Next research step: determine whether the exact inner 4/5-round
cut can be represented as a compact **joint-carry transducer** and use
that to prove n-round impossible cells efficiently; avoid deriving
universal 6/7 restrictions from the five-round outer B5 candidate.

## 2026-11-03: two- and three-word core support geometry

Lean: `Magma/Diffan/OuterCoreCarryGeometry.lean`.

After *exact* deletion of the two outer rounds, the necessary
key-free support for six rounds is equivalent to the four-edge
difference diamond

```text
(0,a) -> (a,p) -> (p,q) -> (q,s) -> (s,0)
```

with just two unknown 32-bit differences p,q. The four
`keyFreePossible` constraints are exactly:
`F(a,p)`, `F(p,q XOR a)`, `F(q,s XOR p)`, `F(s,q)`.

For seven rounds, the five-edge core forms a pentagon

```text
(0,a) -> (a,p) -> (p,q) -> (q,r) -> (r,s) -> (s,0)
```

with three unknown words p,q,r, and five local constraints:
`F(a,p)`, `F(p,q XOR a)`, `F(q,r XOR p)`,
`F(r,s XOR q)`, `F(s,r)`.

Lean proves `fourCore_path_iff_diamond`,
`fiveCore_path_iff_pentagon`,
`sixRound_outer_zero_of_no_diamond` and
`sevenRound_outer_zero_of_no_pentagon`, all for arbitrary fixed
round-key sequences. It also proves `reverse_path` for ALL n,
and the corresponding diamond/pentagon endpoint symmetries.

**Scope:** the iff results characterize the overapproximating
key-free path relation, not a fixed-master real DDT. The
`keyFreePossible` carry automaton permits independently selected
nibble-local key/base digits, so false positives remain possible.
An efficient exact joint-carry/base correlation solver is the
next substantive target.

### Independent 6/7/8-round one-hot spot check

Fixture: `nround_fixtures/onehot_8_inputs.txt` and
`onehot_8_outputs.txt`. The **first 32 of 64** cells were run
for each round count, starting at RFC round 0.

| Rounds | SAT | UNSAT | TIMEOUT | NOT_RUN |
|---|---:|---:|---:|---:|
| 6 | 9 | 23 | 0 | 32 |
| 7 | 24 | 6 | 2 | 32 |
| 8 | 32 | 0 | 0 | 32 |

All 9+24+32 SAT witnesses were independently replayed with the
Python round evaluator and matrix SHA-256 checked. The two
seven-round timeouts remain UNKNOWN. The selected 32-cell subset
is not an exhaustive result for all one-hot pairs; no monotonicity
claim over all differences or fixed keys follows.

**Big-picture opportunity:** the six/seven outer coefficient is
exactly a four/five inner-round coefficient, so a compact carry
constraint system should keep only two/three intermediate XOR
differences. Building a complete, correlated transducer would
yield stronger *provable* n-round exclusions than treating all
Feistel edges independently.
