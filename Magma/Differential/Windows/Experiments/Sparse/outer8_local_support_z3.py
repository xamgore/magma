#!/usr/bin/env python3
"""Sound outer-8 relaxation: six independent TRUE Magma round supports.

The full 8-round outer differential (a,0)->(0,s) exactly reduces to a
6-round inner differential (0,a)->(s,0). Let its word differences be
[0,a,p,q,r,t,s,0]. All six g-derivatives must be realized for
some key and base, with the CORRECT Magma S-box and add/rotate operations.

We deliberately allow *independent* 32-bit key/base choices at each
of the six inner rounds. This overapproximates real reachability, so
UNSAT is a sound key-independent obstruction (assuming Z3 correctness).
SAT is only local compatibility, NOT a real Feistel trajectory.

Run:
  python3 Magma/Differential/Windows/Experiments/Sparse/outer8_local_support_z3.py
  python3 Magma/Differential/Windows/Experiments/Sparse/outer8_local_support_z3.py --all

This checks the already independently replayed 32x32 matrix and then
tests all 5 nibble rectangles with unrestricted nonzero nibble values.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[5]))
import argparse
import collections
import hashlib
import json
from pathlib import Path
import subprocess
import time

from z3 import *
from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX, g as real_g

parser = argparse.ArgumentParser()
parser.add_argument("--all", action="store_true", help="check all 1024 cells, not just 80 UNSAT")
parser.add_argument("--timeout-ms", type=int, default=3000)
args = parser.parse_args()

root = Path(__file__).resolve().parents[5]
meta_dir = root / "Magma/Differential/Windows/Experiments/SAT/runs/onehot32_8"
meta = json.loads((meta_dir / "meta.json").read_text())
assert meta["settings"]["rounds"] == 8
assert meta["settings"]["window_start"] == 0
assert meta["settings"]["mode"] == "universal"
assert meta["scenarios"][0]["id"] == "all_keys"
scenario = meta["scenarios"][0]
compressed = (meta_dir / scenario["filename"]).read_bytes()
assert hashlib.sha256(compressed).hexdigest() == scenario["sha256_compressed"]
matrix = subprocess.check_output(
    ["zstd", "-qdc", str(meta_dir / scenario["filename"])]
)
assert len(matrix) == 1024 and matrix.count(2) == 80 and matrix.count(1) == 944

SBOX64 = [sum(int(v) << (4 * digit) for digit, v in enumerate(row)) for row in BOX]
def lookup(nib, packed):
    """A nibble lookup as one 64-bit constant logical shift."""
    return Extract(3, 0, LShR(BitVecVal(packed, 64), ZeroExt(60, nib) << 2))

def sbox_expr(v):
    return Concat(*[
        lookup(Extract(4 * i + 3, 4 * i, v), SBOX64[i])
        for i in range(7, -1, -1)
    ])

def g_expr(k, x):
    return RotateLeft(sbox_expr(k + x), 11)

# Verify the completely separate Z3 bitvector transcription against
# the ordinary Python Magma evaluator, including carries and rotation.
for k, x in [(0, 0), (1, 2), (0xffffffff, 0x12345678),
             (0xc003eafb, 0x12300fe0), (0x11223344, 0x55667788)]:
    got = simplify(g_expr(BitVecVal(k, 32), BitVecVal(x, 32))).as_long()
    assert got == real_g(k, x), (k, x, got, real_g(k, x))

a, s, p, q, r, t = [BitVec(v, 32) for v in ("a", "s", "p", "q", "r", "t")]
d = [BitVecVal(0, 32), a, p, q, r, t, s, BitVecVal(0, 32)]
solver = Solver()
solver.set(timeout=args.timeout_ms)
for i in range(6):
    ki = BitVec(f"key_{i}", 32)
    xi = BitVec(f"base_{i}", 32)
    solver.add((g_expr(ki, xi) ^ g_expr(ki, xi ^ d[i + 1]))
               == (d[i] ^ d[i + 2]))

started = time.monotonic()
results = {}
for i in range(32):
    for j in range(32):
        expected = matrix[32*i + j]
        assert expected in (1, 2)
        if not args.all and expected != 2:
            continue
        solver.push()
        solver.add(a == BitVecVal(1 << i, 32),
                   s == BitVecVal(1 << j, 32))
        answer = str(solver.check())
        solver.pop()
        results[(i, j)] = answer
        if (expected == 1 and answer != "sat") or (expected == 2 and answer != "unsat"):
            print("MISMATCH",i,j,"matrix",expected,"local_support",answer,flush=True)
        if i % 4 == 3 and j == 31:
            print("CHECKED",len(results),"ELAPSED",round(time.monotonic()-started,2),flush=True)

hist = dict(collections.Counter(
    (matrix[i*32+j], res) for (i,j),res in results.items()
))
print("LOCAL_SUPPORT_VS_REAL_SAT_MATRIX",hist,flush=True)

# Test entire 4-bit *nibble-supported* spaces (not just one-hot bits).
rectangles = [(5,7),(6,7),(7,5),(7,6),(7,7)]
rect = {}
for ni,nj in rectangles:
    solver.push()
    ai = 0xf << (4*ni)
    sj = 0xf << (4*nj)
    solver.add(a != 0, s != 0,
               (a & BitVecVal((~ai)&0xffffffff,32)) == 0,
               (s & BitVecVal((~sj)&0xffffffff,32)) == 0)
    answer = str(solver.check())
    if answer == "sat":
        model = solver.model()
        rect[(ni,nj)] = dict(result=answer,
                             a=f"0x{model[a].as_long():08x}",
                             s=f"0x{model[s].as_long():08x}")
    else:
        rect[(ni,nj)] = dict(result=answer)
    solver.pop()
    print("NIBBLE_RECTANGLE",ni,nj,rect[(ni,nj)],flush=True)

report = {
    "rounds": 8,
    "model": "independent genuine one-round Magma g-difference supports",
    "overapproximation": True,
    "proof_status": "Z3 computation, not Lean UNSAT proof",
    "z3_sat_status_comparison": {str(k):v for k,v in hist.items()},
    "nibble_rectangles": {f"{i},{j}":v for (i,j),v in rect.items()},
    "elapsed_seconds": round(time.monotonic()-started,3),
}
(meta_dir / "independent_local_support_z3.json").write_text(json.dumps(report,indent=2)+"\n")
print("DONE",len(results),"PAIRS",report["elapsed_seconds"],"SECONDS",flush=True)
