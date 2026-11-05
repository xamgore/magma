#!/usr/bin/env python3
"""Exact conditional 32-bit five-round triple-carry fiber, at FIXED middle base h.

Proves computationally (through exhaustive finite-state contraction,
not a Lean theorem) the count of r with given keys k1,k2,k3, a,b,h:

  c = gDiff(k1,r,a)
  z = inverse_g(k2,h)  [uniquely determined]
  gDiff(k2,z,c) = a XOR b
  gDiff(k3,r XOR h,b) = c.

The weighted DP runs eight real RFC S-box nibbles with all six
correlated carries. One rotation tag stream E is initially unknown;
its 11 cyclic boundary bits are guessed (2048 cases), and closure
is checked as the last three digits are generated.

This is an EXACT count for one fixed h; it does NOT sum over all h
and is NOT a full five-round DDT or an unconditional speed claim.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import collections
import functools
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX, g as genuine_g
from Magma.Differential.ThreeRounds.Experiments.triple_carry_nibble_probe import triple_word, check_word_trace

MASK = 0xffffffff


def nibble(w, i):
    return (w >> (4 * i)) & 15


def rol11(w):
    return ((w << 11) | (w >> 21)) & MASK


def ror11(w):
    return ((w >> 11) | (w << 21)) & MASK


def inverse_g(k, h):
    """Invert all eight RFC S-boxes, rotation and addition."""
    raw = ror11(h)
    v = 0
    for i in range(8):
        v |= BOX[i].index(nibble(raw, i)) << (4 * i)
    z = (v - k) & MASK
    assert genuine_g(k, z) == h
    return z


def step(i, kdigit, ddigit, xdigit, incoming):
    """Return (base output, XOR output, outgoing two-bit carry state)."""
    c0 = (incoming >> 0) & 1
    c1 = (incoming >> 1) & 1
    a = xdigit + kdigit + c0
    b = (xdigit ^ ddigit) + kdigit + c1
    u = BOX[i][a & 15]
    v = BOX[i][b & 15]
    return u, u ^ v, ((a >> 4) | ((b >> 4) << 1))


def local_tables(k1, k2, k3, a, b, z, h):
    """Small deterministic fixed-key, fixed-h nibble transition LUTs."""
    first, mid, third = [], [], []
    for i in range(8):
        aa = nibble(a, i)
        bb = nibble(b, i)
        rr = nibble(k1, i)
        mm = nibble(k2, i)
        tt = nibble(k3, i)
        zz = nibble(z, i)
        hi = nibble(h, i)
        pre = nibble(ror11(a ^ b), i)
        first.append([[step(i, rr, aa, r, c) for r in range(16)]
                      for c in range(4)])
        mid.append([[step(i, mm, d, zz, c) for d in range(16)]
                    for c in range(4)])
        third.append([[step(i, tt, bb, w, c) for w in range(16)]
                      for c in range(4)])
        assert genuine_g(k2, z) == h
        # Every genuine base addition carry from fixed z agrees with
        # its actual middle S-box output; dynamic delta carries vary.
        assert nibble(ror11(h), i) in BOX[i]
    return first, mid, third


def conditional_count(k1, k2, k3, a, b, h,
                      max_frontier=250000, max_edges=15000000):
    z = inverse_g(k2, h)
    f1, fm, f3 = local_tables(k1, k2, k3, a, b, z, h)
    target = [nibble(ror11(a ^ b), i) for i in range(8)]
    h_digits = [nibble(h, i) for i in range(8)]

    total = 0
    edges_seen = 0
    max_seen = 0
    accepting_seeds = 0
    per_digit_max = [0] * 8
    started = time.monotonic()

    # E5 high 3, E6 full 4, E7 full 4: 2**11 = 2048
    # cyclic boundary guesses. E5 low bit is NOT guessed: by the
    # time it is needed (i7), the actual E5 will have been emitted.
    for g5high in range(8):
        for g6 in range(16):
            for g7 in range(16):
                # 6 carry bits, three last 4-bit E outputs:
                # [ca(2),cb(2),cc(2), E_(i-3),E_(i-2),E_(i-1)]
                seed_state = ((g5high << 1) << 6) | (g6 << 10) | (g7 << 14)
                dist = {seed_state: 1}
                for i in range(8):
                    nxt = collections.defaultdict(int)
                    for st, multiplicity in dist.items():
                        ca, cb, cc = st & 3, (st >> 2) & 3, (st >> 4) & 3
                        ep3 = (st >> 6) & 15
                        ep2 = (st >> 10) & 15
                        ep1 = (st >> 14) & 15
                        cin = (ep3 >> 1) | ((ep2 & 1) << 3)
                        mid_u, mid_delta, cb2 = fm[i][cb][cin]
                        if mid_delta != target[i]:
                            continue
                        assert mid_u == nibble(ror11(h), i)
                        for rdigit in range(16):
                            _, e, ca2 = f1[i][ca][rdigit]
                            if i == 5 and (e >> 1) != g5high:
                                continue
                            if i == 6 and e != g6:
                                continue
                            if i == 7 and e != g7:
                                continue
                            wdigit = rdigit ^ h_digits[i]
                            _, last_delta, cc2 = f3[i][cc][wdigit]
                            if last_delta != e:
                                continue
                            out = (ca2 | (cb2 << 2) | (cc2 << 4) |
                                   (ep2 << 6) | (ep1 << 10) | (e << 14))
                            nxt[out] += multiplicity
                            edges_seen += 1
                    dist = nxt
                    max_seen = max(max_seen, len(dist))
                    per_digit_max[i] = max(per_digit_max[i], len(dist))
                    if max_seen > max_frontier or edges_seen > max_edges:
                        raise RuntimeError(
                            f"frontier_limit_exceeded at nibble {i}: "
                            f"max_frontier={max_seen}, edges={edges_seen}")
                    if not dist:
                        break
                subtotal = sum(dist.values())
                total += subtotal
                accepting_seeds += int(subtotal > 0)

    return total, {
        "fixed_h": f"0x{h:08x}",
        "unique_z": f"0x{z:08x}",
        "cyclic_seed_guesses": 2048,
        "accepting_seeds": accepting_seeds,
        "carry_bits": 6,
        "cyclic_seed_bits": 11,
        "max_frontier": max_seen,
        "max_frontier_by_digit": per_digit_max,
        "accepted_local_edges": edges_seen,
        "seconds": round(time.monotonic() - started, 3),
        "exact_conditional_count": total,
    }


def known_positive_fixtures():
    """Actual 5-round Magma witnesses already Lean-certified in repo."""
    return [
        dict(name="one-hot to four-hot",
             keys=(0, 0x2056, 0xfdfa7789, 0xf0f8d960, 0),
             left=0x9e2641a9, right=0x3754c03d,
             a=0x00000080, b=0xc0000820),
        dict(name="two-hot to three-hot",
             keys=(0, 0xb3900250, 0xddfc38c3, 0xca24f050, 0),
             left=0x9d651eb2, right=0x17714960,
             a=0x80000080, b=0x20200020),
    ]


def witness_fiber(f):
    k0, k1, k2, k3, k4 = f["keys"]
    left0, right0 = f["left"], f["right"]
    r = left0 ^ genuine_g(k0, right0)
    z = genuine_g(k1, r) ^ right0
    h = genuine_g(k2, z)
    ctx = triple_word(k1, k2, k3, f["a"], f["b"], r, z)
    check_word_trace(ctx)
    assert ctx["accepted"] and ctx["h"] == h
    assert inverse_g(k2, h) == z
    return (k1, k2, k3, f["a"], f["b"], h, r, z)


def z3_enumerate_conditional(k1, k2, k3, a, b, h, count, timeout_ms=30000):
    """Independent exact #SMT for small counts; otherwise explicitly skip."""
    if count > 256:
        return {"status": "skipped_count_gt_256", "count": None}
    from z3 import BitVec, BitVecVal, Concat, Extract, LShR, RotateLeft
    from z3 import Solver, ZeroExt, sat, unsat
    lut = [sum(int(v) << (4 * j) for j, v in enumerate(box)) for box in BOX]

    def G(k, x):
        t = k + x
        substituted = Concat(*[
            Extract(3, 0, LShR(
                BitVecVal(lut[i], 64),
                ZeroExt(60, Extract(4 * i + 3, 4 * i, t)) << 2))
            for i in range(7, -1, -1)
        ])
        return RotateLeft(substituted, 11)

    w = BitVec("r_candidate", 32)
    K1, K2, K3 = [BitVecVal(k, 32) for k in (k1, k2, k3)]
    A, B, H = [BitVecVal(v, 32) for v in (a, b, h)]
    z = BitVecVal(inverse_g(k2, h), 32)
    c = G(K1, w ^ A) ^ G(K1, w)
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(
        (G(K2, z ^ c) ^ G(K2, z)) == (A ^ B),
        (G(K3, (w ^ H) ^ B) ^ G(K3, w ^ H)) == c,
    )
    found = []
    begin = time.monotonic()
    while len(found) <= count:
        result = solver.check()
        if result == unsat:
            assert len(found) == count, (len(found), count)
            return {"status": "exact_verified_by_independent_Z3",
                    "count": len(found), "seconds": round(time.monotonic()-begin, 3)}
        if result != sat:
            return {"status": "unknown", "count_lower_bound": len(found),
                    "seconds": round(time.monotonic()-begin, 3)}
        val = solver.model().eval(w).as_long()
        found.append(val)
        assert len(set(found)) == len(found)
        solver.add(w != BitVecVal(val, 32))
    raise AssertionError("Z3 found more solutions than weighted DP counted")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--fixture", type=int, default=0, choices=(0, 1))
    p.add_argument("--max-frontier", type=int, default=250000)
    p.add_argument("--max-edges", type=int, default=15000000)
    p.add_argument("--z3-check", action="store_true")
    p.add_argument("--z3-timeout-ms", type=int, default=30000)
    p.add_argument("--output", type=Path,
                   default=ROOT / "Magma/Differential/FiveRounds/Experiments/fixed_middle_transfer_report.json")
    args = p.parse_args()
    f = known_positive_fixtures()[args.fixture]
    k1, k2, k3, a, b, h, r, z = witness_fiber(f)
    print("REAL_RFC_WITNESS", f["name"], f"r=0x{r:08x}", f"h=0x{h:08x}", flush=True)
    count, stats = conditional_count(k1, k2, k3, a, b, h,
                                     args.max_frontier, args.max_edges)
    assert count >= 1, "exact conditional fiber lost a known real witness"
    output = {
        "fixture": f["name"],
        "fixed_keys": [f"0x{k:08x}" for k in (k1,k2,k3)],
        "alpha": f"0x{a:08x}", "sigma": f"0x{b:08x}",
        "actual_positive_witness_r": f"0x{r:08x}",
        "stats": stats,
        "scope": "exact fixed-middle-h 32-bit conditional fiber, not full five-round DDT",
        "no_full_9_round_claim": True,
        "proof_status": "Python executable; Lean certifies underlying tagged steps, not the DP count",
    }
    if args.z3_check:
        output["independent_z3_check"] = z3_enumerate_conditional(
            k1, k2, k3, a, b, h, count, args.z3_timeout_ms)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print("EXACT_FIXED_MIDDLE_FIBER",json.dumps(output,sort_keys=True),flush=True)


if __name__=="__main__":
    main()
