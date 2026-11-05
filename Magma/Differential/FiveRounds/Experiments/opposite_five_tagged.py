#!/usr/bin/env python3
"""Independent eight-nibble tagged/carry encoding of the opposite five-round Magma fiber.

This is a SEMANTIC ORACLE for a future weighted five-chain transfer, NOT a fast
carryDP or an improvement over the existing #SMT enumerator.  Every one of the
five real modular additions has TWO explicit, locally propagated carry chains.
The three base-word identities and five derivative identities are linked only
through 11-bit rotation of emitted local S-box tags.

Enumerates complete middle-base pairs (r,z) only if Z3 exhausts to UNSAT.
Never interprets a timeout or a model cap as zero.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX

MASK = 0xffffffff
DEFAULT_KEYS = (0, 0x2056, 0xfdfa7789, 0xf0f8d960, 0)


def local_chain(k, x, difference):
    """Emit base and difference S-box tags using *actual* dual 32-bit carries."""
    from z3 import BitVecVal, Concat, Extract, LShR, ZeroExt

    carry0 = BitVecVal(0, 1)
    carry1 = BitVecVal(0, 1)
    base = []
    derivative = []
    lookup = [sum(v << (4 * i) for i, v in enumerate(box)) for box in BOX]
    for i in range(8):
        xi = Extract(4 * i + 3, 4 * i, x)
        di = Extract(4 * i + 3, 4 * i, difference)
        key_nibble = BitVecVal((k >> (4 * i)) & 15, 5)
        s0 = ZeroExt(1, xi) + key_nibble + ZeroExt(4, carry0)
        s1 = ZeroExt(1, xi ^ di) + key_nibble + ZeroExt(4, carry1)
        table = BitVecVal(lookup[i], 64)
        v0 = Extract(3, 0, LShR(table, ZeroExt(60, Extract(3, 0, s0)) << 2))
        v1 = Extract(3, 0, LShR(table, ZeroExt(60, Extract(3, 0, s1)) << 2))
        base.append(v0)
        derivative.append(v0 ^ v1)
        carry0 = Extract(4, 4, s0)
        carry1 = Extract(4, 4, s1)
    return Concat(*reversed(base)), Concat(*reversed(derivative))


def tagged_solver(keys, a, b, timeout_ms=15000):
    from z3 import BitVec, BitVecVal, RotateLeft, Solver
    assert len(keys) == 5
    x1, r, z, x4, x5 = [
        BitVec(name, 32) for name in ("tag_x1", "tag_r", "tag_z", "tag_x4", "tag_x5")
    ]
    p, q, t = [BitVec(name, 32) for name in ("tag_p", "tag_q", "tag_t")]
    a32, b32 = BitVecVal(a, 32), BitVecVal(b, 32)

    bases = [x1, r, z, x4, x5]
    diffs = [a32, p, q, t, b32]
    results = [local_chain(key, base, diff)
               for key, base, diff in zip(keys, bases, diffs)]
    u = [RotateLeft(v[0], 11) for v in results]
    e = [RotateLeft(v[1], 11) for v in results]

    s = Solver()
    s.set(timeout=timeout_ms)
    # Only these relations close the genuine five-round Feistel fiber.
    s.add(p == e[0], q == a32 ^ e[1], t == p ^ e[2])
    s.add(b32 == q ^ e[3], t == e[4])
    s.add(x1 == z ^ u[1], x4 == r ^ u[2], x5 == z ^ u[3])
    return s, (r, z)


def count_tagged(keys, a, b, timeout_ms=15000, model_cap=100):
    from z3 import BitVecVal, Or, sat, unsat
    solver, (r, z) = tagged_solver(keys, a, b, timeout_ms)
    started = time.monotonic()
    matches = []
    status = "UNKNOWN"
    for n in range(model_cap + 1):
        result = solver.check()
        if result == unsat:
            status = "complete_unsat_after_enumeration"
            break
        if result != sat:
            status = "UNKNOWN"
            break
        m = solver.model()
        rv, zv = (m.eval(r).as_long(), m.eval(z).as_long())
        # Independent 32-bit reference g + direct Feistel replay.
        from Magma.Differential.FiveRounds.Experiments.opposite_five_fiber import five_difference_conditions, middle_to_input, feistel
        assert five_difference_conditions(keys, a, b, rv, zv)[0]
        x0, x1 = middle_to_input(keys, rv, zv)
        f0 = feistel(keys, x0, x1)
        f1 = feistel(keys, x0, x1 ^ a)
        assert (f0[0] ^ f1[0], f0[1] ^ f1[1]) == (b, 0)
        matches.append((rv, zv))
        solver.add(Or(r != BitVecVal(rv, 32), z != BitVecVal(zv, 32)))
        if n + 1 > model_cap:
            status = "model_cap"
            break
    if len(matches) > model_cap:
        status = "model_cap"
    assert len(matches) == len(set(matches))
    canonical = "".join(f"{r:08x}{z:08x}\n" for r, z in sorted(matches))
    return dict(
        status=status,
        count_or_lower_bound=len(matches),
        sha256_sorted_middle_bases=hashlib.sha256(canonical.encode()).hexdigest(),
        sample_pairs=[[f"0x{r:08x}", f"0x{z:08x}"] for r, z in sorted(matches)[:8]],
        seconds=round(time.monotonic() - started, 3),
        implementation="local explicit five dual-carry S-box tag chains",
        caveat="Exact only with complete_unsat_after_enumeration; this is #SMT, not weighted carryDP",
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--keys", default=",".join(hex(k) for k in DEFAULT_KEYS))
    p.add_argument("--alpha", type=lambda v: int(v, 0), default=0x80000000)
    p.add_argument("--beta", type=lambda v: int(v, 0), default=0x681e60a7)
    p.add_argument("--timeout-ms", type=int, default=15000)
    p.add_argument("--model-cap", type=int, default=100)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    keys = tuple(int(v, 0) for v in args.keys.split(","))
    assert len(keys) == 5 and all(0 <= k <= MASK for k in keys)
    assert 0 <= args.alpha <= MASK and 0 <= args.beta <= MASK
    result = count_tagged(keys, args.alpha, args.beta, args.timeout_ms, args.model_cap)
    print("OPPOSITE_TAGGED_FIVE", json.dumps(result, sort_keys=True), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
