# NinePlus: RFC 8891 impossible differentials beyond 8 rounds

**Status (2026-11-03): ACTIVE EXPLORATION — no nine-round impossible differential established.**

This research package intentionally lives inside `Magma/`, alongside
experimental Lean declarations, scripts, fixtures, and small result summaries.
It is **not imported by `Magma.lean`**; heavy or speculative work stays opt-in.

## The testable hypothesis

Nine ordinary Feistel rounds spanning RFC rounds 20..28 have a
palindromic eight-round prefix. After the exact two-boundary deletion,
the seven inner round-key indices are `[5,6,7,7,6,5,4]`.

The same 32-bit key is used more than once. A linked-key local-support
filter may reject transitions that survive an independent-key filter.
All base words remain independent in BOTH models. This tests only
repeated-subkey constraints, *not* true state/base correlation.

Crucial for XOR differences: `(x XOR d)+k != (x+k) XOR d` in general.
Thus a shared additive key cannot be eliminated by reparametrizing
the base word. The library already proves the parity dependence of
the complete one-round row for input difference `1`.

## Lean results and proof status

- `Model.lean`: `IndependentSeven` and `LinkedSeven` model the seven
  interior differences with five free 32-bit words. The theorem
  `linked_implies_independent` is **kernel proved**.
- `Model.lean`: `GainsFromKeyCoupling` specifies a strict filtering
  improvement. `nine_round_zero_if_linked_model_sound` is **conditional**:
  it takes an explicit `sound` argument that must still be established.
  It is NOT a nine-round impossible-differential theorem.
- `ParityCollision.lean`: **kernel proved** local strictness:
  with input difference `0x00000001`, output `0x00001800` requires an
  even key, and `0x00002800` requires an odd key. Both are individually
  achievable, but they cannot be realized with the **same** key.
  This demonstrates real benefit from shared key variables, NOT that
  a particular seven-/nine-round global difference forces the clash.
- These files contain no `sorry` or unproved `axiom`. In future
  speculative modules, explicitly labeled assumptions or `variable`
  may be used; keep them separate from certified claims.

## Executable experiments

`local_key_coupling.py` encodes genuine 32-bit Magma `g` with actual
S-boxes and modular carries in two Z3 models. Both use a **single
per-cell timeout**; the default is now **600000 ms (10 minutes)**.
It also supports unrestricted input/output 64-bit differences via
`--family general` and explicit input/output fixture files.
A checkpoint is atomically saved after every cell, and every local
SAT model is replayed by an independent Python implementation of g.
Run from repository root:

```bash
python3 Magma/NinePlus/local_key_coupling.py --limit 10 --timeout-ms 1500
python3 Magma/NinePlus/local_key_coupling.py --limit 3 --timeout-ms 12000 \
  --output Magma/NinePlus/results/local_support_12s.json
lake build Magma.NinePlus.ParityCollision
```

Full 10-minute-budget Z3 baseline, RFC rounds 20..28:

```bash
python3 Magma/NinePlus/local_key_coupling.py --limit 0 --timeout-ms 600000 \
  --output Magma/NinePlus/results/linked_600s_all64.json
python3 Magma/NinePlus/local_key_coupling.py --family general \
  --input-file Magma/NinePlus/fixtures/general_inputs.txt \
  --output-file Magma/NinePlus/fixtures/general_outputs.txt \
  --start-index 16 --limit 4 --timeout-ms 600000 \
  --output Magma/NinePlus/results/general_linked_600s_row2_first4.json
```

**Observed:** all 64/64 outer cells are SAT in both independent
and schedule-linked local-support models (190.48 s for all cells).
Four previously untested general 64-bit cells with two active halves
are also SAT in both models (19.14 s). No UNSAT or UNKNOWN in either
completed experiment; every local model passes independent Python
evaluation of all g-derivatives. The Z3 timeout is a **limit per
individual query**, not actual computation time.

These are **necessary-support SAT witnesses**, not full-round
Feistel witnesses, and do not prove that the key-linked relaxation
is useless on every difference class.

First 10 sparse outer pairs: independent 10 SAT;
shared-key 2 SAT and 8 UNKNOWN at 1500 ms each.
Three longer checked pairs: both models 3 SAT at 12000 ms.
**No extra UNSAT from key sharing discovered yet.**
Unknown means unresolved — never impossible.

A second full-schedule **general-difference** test (both halves
active) checked the first 16 cells of the 8x8 fixture at window
20..28: 12 SAT, 4 UNKNOWN at 30000 ms. A focused 2x3 retest
with 120000 ms resolved all four UNKNOWN as SAT, with six
independently replayed witnesses. Compact matrix metadata and hashes:
`results/general9_120s_replay.json`. Again, no nine-round
ID found in the tested cells.

For a self-contained audit, `results/sat_runs/` contains four
small original matrices, their SHA-256 metadata, compressed SAT
witnesses and independent verification reports. Re-run all witnesses:

```bash
python3 research/verify_nround.py   Magma/NinePlus/results/sat_runs/round9_window20_general_hard6_120s
```

The old `reflection_window20.py`, original 8x8 outer inputs/outputs,
and baseline evidence have been preserved by Git history-aware moves.
See `BASELINE_2026-11-03.md` and `fixtures/`.
Old complete SAT runs live under ignored `research/nround_runs/`.
The reusable Rust runner is `research/magma_exact_matrix_nround.rs`.

You may set `--timeout-ms 86400000` (24 hours) for a nominated hard
query, but don't saturate a whole matrix with 24-hour cells before
observing useful partial progress. Check logs and keep `unknown`
distinct from `unsat`. Independent replay of SAT witnesses is mandatory.

## Next *meaningful* gate

1. Demonstrate a concrete **pair of endpoint differences** satisfying
   `IndependentSeven` but refuting `LinkedSeven` (or admit that this
   model alone has no detectable advantage on the chosen class).
2. Prove that the linked relation soundly overapproximates a genuine
   nine-round RFC schedule *only if that gate is promising*.
3. Recheck any `unsat` under the full Rust SAT model; if one survives,
   look for a parameterized family and an application to 10+ rounds.
4. Prefer stronger shared-base/carry-state constraints if linked-key
   local supports remain SAT. Do not formalize another bulk SAT table.

**Design freeze:** `DESIGN_FREEZE.md`. The original large research
history remains in `research/archive/SPARSE_WINDOWS_HISTORY.md`.
