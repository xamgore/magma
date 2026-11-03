#!/usr/bin/env python3
"""Compare independent-key and RFC-shared-key genuine Magma g-support.

Both models keep the per-round 32-bit base words independent. They are
NECESSARY outer/general Feistel differential-support relaxations, not
sufficient proof of any real complete master-key trajectory.

SAT: independently replayed for every local g-derivative.
UNSAT: Z3 computational exclusion of that relaxation (not Lean proof).
UNKNOWN: no conclusion. Per-cell timeout defaults to TEN MINUTES.
A checkpoint JSON is atomically rewritten after every finished cell.
"""
import argparse
import collections
import json
import sys
import time
from pathlib import Path

from z3 import (
    BitVec, BitVecVal, Concat, Extract, LShR,
    RotateLeft, Solver, ZeroExt, simplify,
)

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
from verify_nround import BOX, g as plain_g, key_index

parser = argparse.ArgumentParser()
parser.add_argument("--family", choices=("outer", "general"), default="outer")
parser.add_argument("--input-file", type=Path, help="64-bit difference list for --family general")
parser.add_argument("--output-file", type=Path, help="64-bit difference list for --family general")
parser.add_argument("--window-start", type=int, default=20)
parser.add_argument("--rounds", type=int, default=9)
parser.add_argument("--timeout-ms", type=int, default=600000)
parser.add_argument("--limit", type=int, default=8, help="0 means all remaining cells")
parser.add_argument("--start-index", type=int, default=0, help="0-based index in the chosen ordering")
parser.add_argument("--output", type=Path, help="checkpoint JSON")
cfg = parser.parse_args()
assert 5 <= cfg.rounds <= 32 and 0 <= cfg.window_start <= 32 - cfg.rounds
assert 0 <= cfg.limit <= 4096 and cfg.timeout_ms > 0

LUT = [sum(int(v) << (4 * j) for j, v in enumerate(box)) for box in BOX]


def G(k, x):
    """Bitvector RFC Magma g: rotate-left-11 of 8 nibble substitutions."""
    t = k + x
    y = Concat(*[
        Extract(3, 0, LShR(BitVecVal(LUT[i], 64),
            ZeroExt(60, Extract(4 * i + 3, 4 * i, t)) << 2))
        for i in range(7, -1, -1)
    ])
    return RotateLeft(y, 11)


for k, x in [(0, 0), (1, 2), (0xffffffff, 0x12345678),
             (0x55555555, 0xaaaaaaab)]:
    assert simplify(G(BitVecVal(k, 32), BitVecVal(x, 32))).as_long() == plain_g(k, x)


def load_words(path):
    assert path is not None and path.is_file(), path
    values = []
    for line in path.read_text().splitlines():
        line = line.split("#")[0].strip()
        if line:
            v = int(line, 0)
            assert 0 <= v < 2**64
            values.append(v)
    assert values
    return values


outer_values = [
    1, 0x00100000, 0x01000000, 0x10000000,
    0x10000001, 0x10100000, 0x81000000, 0x90000000,
]
if cfg.family == "outer":
    assert cfg.input_file is None and cfg.output_file is None
    inputs = [v << 32 for v in outer_values]
    outputs = outer_values
    n = cfg.rounds - 2  # exact deletion of outer first/last rounds
    indices = [key_index(i) for i in range(
        cfg.window_start + 1, cfg.window_start + cfg.rounds - 1)]
    a = BitVec("a", 32)
    s = BitVec("s", 32)
    delta = [BitVecVal(0, 32), a] + [
        BitVec(f"d{i}", 32) for i in range(2, n)
    ] + [s, BitVecVal(0, 32)]
else:
    inputs = load_words(cfg.input_file)
    outputs = load_words(cfg.output_file)
    n = cfg.rounds
    indices = [key_index(i) for i in range(
        cfg.window_start, cfg.window_start + cfg.rounds)]
    aL, aR, bL, bR = [BitVec(x, 32) for x in ("aL", "aR", "bL", "bR")]
    delta = [aL, aR] + [
        BitVec(f"d{i}", 32) for i in range(2, n)
    ] + [bL, bR]

assert len(delta) == n + 2 and len(indices) == n
print("FAMILY", cfg.family, "INNER_KEY_INDICES" if cfg.family == "outer"
      else "FULL_KEY_INDICES", indices, flush=True)

base = [BitVec(f"x{i}", 32) for i in range(n)]
master = [BitVec(f"K{i}", 32) for i in range(8)]
separate = [BitVec(f"free_key{i}", 32) for i in range(n)]


def mkmodel(linked):
    solver = Solver()
    solver.set(timeout=cfg.timeout_ms)
    for i in range(n):
        k = master[indices[i]] if linked else separate[i]
        solver.add((G(k, base[i] ^ delta[i + 1]) ^ G(k, base[i]))
                   == (delta[i] ^ delta[i + 2]))
    return solver


models = {"independent": mkmodel(False), "key_linked": mkmodel(True)}


def conditions(alpha, beta):
    if cfg.family == "outer":
        return (a == BitVecVal(alpha >> 32, 32),
                s == BitVecVal(beta, 32))
    return (
        aL == BitVecVal(alpha >> 32, 32),
        aR == BitVecVal(alpha & 0xffffffff, 32),
        bL == BitVecVal(beta >> 32, 32),
        bR == BitVecVal(beta & 0xffffffff, 32),
    )


def replay_local(solver, linked, alpha, beta):
    """Recheck every SAT local g-equation using independent Python RFC g."""
    model = solver.model()
    def value(expr):
        return model.eval(expr, model_completion=True).as_long()
    ds = [value(q) for q in delta]
    if cfg.family == "outer":
        # Two exact boundary rounds were deleted; inner endpoints
        # are (0, alpha.left) -> (beta.right, 0).
        assert (ds[0], ds[1]) == (0, alpha >> 32)
        assert (ds[-2], ds[-1]) == (beta & 0xffffffff, 0)
    else:
        assert (ds[0], ds[1]) == (alpha >> 32, alpha & 0xffffffff)
        assert (ds[-2], ds[-1]) == (beta >> 32, beta & 0xffffffff)
    for i in range(n):
        k = value(master[indices[i]] if linked else separate[i])
        x = value(base[i])
        assert (plain_g(k, x ^ ds[i + 1]) ^ plain_g(k, x)) == (
            ds[i] ^ ds[i + 2]), (i, k, x)


pairs = [(i, j) for i in range(len(inputs)) for j in range(len(outputs))]
if cfg.family == "outer":
    # Revisit previously hard 5-second RFC window-20 outer cells first.
    prior = [
        (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (0, 7),
        (1, 1), (1, 4), (2, 4), (2, 7), (4, 0), (4, 1),
        (4, 2), (4, 4), (4, 5), (4, 6), (4, 7),
        (5, 0), (5, 4), (5, 7), (6, 0), (7, 4),
    ]
    pairs = prior + [p for p in pairs if p not in prior]
assert 0 <= cfg.start_index < len(pairs)
pairs = pairs[cfg.start_index:]
if cfg.limit:
    pairs = pairs[:cfg.limit]

dest = cfg.output or ROOT / "Magma/NinePlus/results/local_support.json"
dest.parent.mkdir(parents=True, exist_ok=True)
completed = []
started = time.monotonic()


def save_report(final=False):
    counts = collections.Counter(
        (r["independent"], r["key_linked"]) for r in completed)
    report = {
        "family": cfg.family,
        "rounds": cfg.rounds,
        "window_start": cfg.window_start,
        "rfc_key_indices": indices,
        "timeout_ms": cfg.timeout_ms,
        "start_index": cfg.start_index,
        "planned_cells": len(pairs),
        "completed_cells": len(completed),
        "input_difference_hex": [f"0x{v:016x}" for v in inputs],
        "output_difference_hex": [f"0x{v:016x}" for v in outputs],
        "observations": completed,
        "summary": {str(k): v for k, v in counts.items()},
        "elapsed_seconds": round(time.monotonic() - started, 1),
        "status": "complete" if final else "in_progress",
        "proof_status": "Z3 only; local SAT replayed; UNKNOWN not UNSAT",
    }
    temp = dest.with_suffix(dest.suffix + ".tmp")
    temp.write_text(json.dumps(report, indent=2) + "\n")
    temp.replace(dest)
    return report


save_report()
for i, j in pairs:
    alpha, beta = inputs[i], outputs[j]
    row = {"i": i, "j": j, "alpha": f"{alpha:016x}", "beta": f"{beta:016x}"}
    for label, solver in models.items():
        solver.push()
        solver.add(*conditions(alpha, beta))
        tick = time.monotonic()
        row[label] = str(solver.check())
        row[label + "_ms"] = round((time.monotonic() - tick) * 1000)
        if row[label] == "sat":
            replay_local(solver, label == "key_linked", alpha, beta)
            row[label + "_sat_replayed"] = True
        solver.pop()
    assert not (row["independent"] == "unsat" and row["key_linked"] == "sat")
    completed.append(row)
    save_report()
    print("CELL", json.dumps(row, sort_keys=True), flush=True)

report = save_report(final=True)
print("REPORT", dest, "SUMMARY", report["summary"], flush=True)
