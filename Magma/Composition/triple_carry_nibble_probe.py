#!/usr/bin/env python3
"""One-nibble exact three-carry join for RFC Magma: executable P0 prototype.

This is NOT a fast 32-bit / five-round DDT algorithm. It demonstrates
a genuinely *local* triple-derivative constraint with the REAL
substitution tables, two 4-bit modular additions per g, three pairs
of carries, shared per-nibble base variables and rotate-left-11
cross-nibble tag dependencies. Every digit claim is independently
checked against the complete Python RFC g evaluator.

Use from the repo root:
  python3 Magma/Composition/triple_carry_nibble_probe.py
  python3 Magma/Composition/triple_carry_nibble_probe.py --cases 1000

The corresponding per-round Lean semantics are established in
Magma/Composition/TaggedCarryWord.lean.
"""
import argparse
import collections
import hashlib
import json
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
from verify_nround import BOX, g as reference_g

MASK32 = 0xffffffff


def rol11(x):
    return ((x << 11) | (x >> 21)) & MASK32


def ror11(x):
    return ((x >> 11) | (x << 21)) & MASK32


def nibble(x, i):
    return (x >> (4 * i)) & 15


def pack(ds):
    assert len(ds) == 8
    return sum(v << (4 * i) for i, v in enumerate(ds))


def mixed_digit(tags, i):
    """i-th nibble after cyclic 32-bit rotate-left-11.

    Output bit positions 0..2 originate at bits 1..3 of
    nibble i-3; output bit position 3 originates at bit 0
    of nibble i-2. Indices are modulo 8.
    """
    return ((tags[(i - 3) % 8] >> 1) |
            ((tags[(i - 2) % 8] & 1) << 3))


def tagged_step(i, k, diff, x, state):
    """Return (base S-box digit, XOR derivative digit, next carries)."""
    assert all(0 <= v < 16 for v in (k, diff, x))
    c0, c1 = state
    assert c0 in (0, 1) and c1 in (0, 1)
    sum0 = x + k + c0
    sum1 = (x ^ diff) + k + c1
    y0 = BOX[i][sum0 & 15]
    y1 = BOX[i][sum1 & 15]
    return y0, y0 ^ y1, (sum0 >> 4, sum1 >> 4)


def full_tagged_trace(k, d, x):
    """The actual sequence of eight taggedCarrySteps, with both carry chains."""
    state = (0, 0)
    initial = state
    base_tags, diff_tags, incoming = [], [], []
    for i in range(8):
        incoming.append(state)
        base, derivative, state = tagged_step(
            i, nibble(k, i), nibble(d, i), nibble(x, i), state)
        base_tags.append(base)
        diff_tags.append(derivative)
    assert initial == (0, 0)
    assert rol11(pack(base_tags)) == reference_g(k, x)
    assert rol11(pack(diff_tags)) == (reference_g(k, x ^ d) ^ reference_g(k, x))
    return {
        "base_tags": base_tags,
        "diff_tags": diff_tags,
        "incoming": incoming,
        "end_carries": state,
    }


def triple_word(k1, k2, k3, a, b, r, z):
    """Exact five-round inner triple, reparameterized by z=g_k2^-1(h).

    e = (g_k1(r XOR a) XOR g_k1(r)).ror11
    c = rol11(e)
    middle input XOR difference = c
    U = t(z+k2); h=rol11(U)
    third base word w = r XOR h
    The two extra acceptance tests are:
      gDiff(k2,z,c) == a XOR b
      gDiff(k3,w,b) == c
    """
    t1 = full_tagged_trace(k1, a, r)
    e = t1["diff_tags"]
    c = rol11(pack(e))
    t2 = full_tagged_trace(k2, c, z)
    u = t2["base_tags"]
    h = rol11(pack(u))
    w = r ^ h
    t3 = full_tagged_trace(k3, b, w)
    target2 = ror11(a ^ b)
    acc2 = pack(t2["diff_tags"]) == target2
    acc3 = pack(t3["diff_tags"]) == pack(e)
    return dict(
        t1=t1, t2=t2, t3=t3,
        c=c, h=h, w=w,
        target2=target2,
        accepted=acc2 and acc3,
        a=a, b=b, r=r, z=z, keys=(k1, k2, k3),
    )


def triple_local_step(ctx, i, r_digit, z_digit):
    """One exact nibble factor, with a six-carry and delayed-tag boundary.

    ctx is a FULL word trace from which the boundary carries and
    delayed E/U tags were read. The current r,z nibbles are free,
    so this produces a genuine 16x16 local transfer table at that
    boundary, not just a check of one preselected assignment.
    """
    t1, t2, t3 = ctx["t1"], ctx["t2"], ctx["t3"]
    k1, k2, k3 = ctx["keys"]
    e_old = t1["diff_tags"]
    u_old = t2["base_tags"]
    ca = t1["incoming"][i]
    cb = t2["incoming"][i]
    cc = t3["incoming"][i]

    base1, e, next_ca = tagged_step(
        i, nibble(k1, i), nibble(ctx["a"], i), r_digit, ca)
    input_middle = mixed_digit(e_old, i)
    base2, f, next_cb = tagged_step(
        i, nibble(k2, i), input_middle, z_digit, cb)
    w_digit = r_digit ^ mixed_digit(u_old, i)
    _, g, next_cc = tagged_step(
        i, nibble(k3, i), nibble(ctx["b"], i), w_digit, cc)
    target = nibble(ctx["target2"], i)

    return {
        "accepted": (f == target and g == e),
        "e": e,
        "u": base2,
        "f": f,
        "g": g,
        "target": target,
        "next_carries": next_ca + next_cb + next_cc,
        "first_base_tag": base1,
    }


def check_word_trace(ctx):
    """Compare ALL local constraints against direct three g-derivatives."""
    e = ctx["t1"]["diff_tags"]
    u = ctx["t2"]["base_tags"]
    for i in range(8):
        assert nibble(ctx["c"], i) == mixed_digit(e, i)
        assert nibble(ctx["h"], i) == mixed_digit(u, i)
        assert nibble(ctx["w"], i) == (
            nibble(ctx["r"], i) ^ mixed_digit(u, i))
        r_i, z_i = nibble(ctx["r"], i), nibble(ctx["z"], i)
        out = triple_local_step(ctx, i, r_i, z_i)
        assert out["e"] == e[i]
        assert out["u"] == u[i]
        assert out["f"] == ctx["t2"]["diff_tags"][i]
        assert out["g"] == ctx["t3"]["diff_tags"][i]
        assert out["next_carries"] == (
            (ctx["t1"]["incoming"][i + 1] if i < 7
             else ctx["t1"]["end_carries"]) +
            (ctx["t2"]["incoming"][i + 1] if i < 7
             else ctx["t2"]["end_carries"]) +
            (ctx["t3"]["incoming"][i + 1] if i < 7
             else ctx["t3"]["end_carries"])
        )
    local_accept = all(triple_local_step(
        ctx, i, nibble(ctx["r"], i), nibble(ctx["z"], i))["accepted"]
        for i in range(8))
    assert local_accept == ctx["accepted"]
    k1, k2, k3 = ctx["keys"]
    a, b, r, z = ctx["a"], ctx["b"], ctx["r"], ctx["z"]
    c, h = ctx["c"], ctx["h"]
    genuine = (
        reference_g(k2, z ^ c) ^ reference_g(k2, z) == (a ^ b)
        and reference_g(k3, (r ^ h) ^ b) ^
            reference_g(k3, (r ^ h)) == c
    )
    assert genuine == ctx["accepted"]


def probe_row(ctx, i):
    """Count 16^2 choices of r_i,z_i at one fixed, real boundary."""
    histogram = collections.Counter()
    accepted = 0
    for r in range(16):
        for z in range(16):
            out = triple_local_step(ctx, i, r, z)
            if out["accepted"]:
                accepted += 1
                # Distinct following states retain all six carry bits,
                # the emitted first-difference nibble and the second
                # base-output nibble; these latter two are necessary
                # to feed later rotate-left-11 constraints.
                state = (*out["next_carries"], out["e"], out["u"])
                histogram[state] += 1
    assert accepted == sum(histogram.values())
    return {
        "digit_index": i,
        "assignments": 256,
        "accepted_assignments": accepted,
        "distinct_next_tagged_states": len(histogram),
        "max_multiplicity": max(histogram.values(), default=0),
        "min_multiplicity": min(histogram.values(), default=0),
    }


def check_certified_five_round_positive_fixtures():
    """Reuse two known Lean-kernel-checked real Magma DDT positives.

    The independent base witness is recorded in
    OneHotFourHotPositive.lean and SparsePositiveWitnesses.lean.
    The exact five-round outer identity reduces the first and last
    rounds; the inner three-round coordinates are
      r = right half after round 0,
      z = g(k1,r) XOR left half after round 0.
    This is NOT an arbitrary fit of r,z to an output.
    """
    fixtures = [
        dict(name='Lean one-hot to four-hot',
             keys=(0,0x2056,0xfdfa7789,0xf0f8d960,0),
             left=0x9e2641a9,right=0x3754c03d,
             a=0x00000080,b=0xc0000820),
        dict(name='Lean two-hot to three-hot',
             keys=(0,0xb3900250,0xddfc38c3,0xca24f050,0),
             left=0x9d651eb2,right=0x17714960,
             a=0x80000080,b=0x20200020),
    ]
    results=[]
    for fixture in fixtures:
        k0,k1,k2,k3,k4=fixture['keys']
        def five(left,right):
            for k in fixture['keys']:
                left,right=right,left^reference_g(k,right)
            return left,right
        l0,r0=fixture['left'],fixture['right']
        a,b=fixture['a'],fixture['b']
        y0=five(l0,r0)
        y1=five(l0^a,r0)
        assert (y0[0]^y1[0],y0[1]^y1[1])==(0,b)
        # Actual base immediately after the first Feistel round.
        first_left,first_right=r0, l0^reference_g(k0,r0)
        r=first_right
        z=reference_g(k1,r)^first_left
        ctx=triple_word(k1,k2,k3,a,b,r,z)
        check_word_trace(ctx)
        assert ctx['accepted'],(fixture['name'],'triple rejected true Magma witness')
        rows=[probe_row(ctx,i) for i in range(8)]
        assert all(row['accepted_assignments']>0 for row in rows)
        result=dict(name=fixture['name'],
            a=f'0x{a:08x}',b=f'0x{b:08x}',
            inner_r=f'0x{r:08x}',inner_z=f'0x{z:08x}',
            true_triple_accepted=True,
            local_accepted_counts=[v['accepted_assignments'] for v in rows],
            local_distinct_next_states=[v['distinct_next_tagged_states'] for v in rows])
        results.append(result)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=384)
    ap.add_argument("--seed", type=int, default=8891)
    ap.add_argument("--output", type=Path,
                    default=ROOT / "Magma/Composition/tagged_triple_probe.json")
    args = ap.parse_args()
    assert args.cases >= 16
    rng = random.Random(args.seed)
    started = time.monotonic()
    # Independent rotation check covers all 8 nibble positions:
    for _ in range(128):
        ds = [rng.randrange(16) for _ in range(8)]
        rot = rol11(pack(ds))
        for i in range(8):
            assert nibble(rot, i) == mixed_digit(ds, i)

    rows = []
    accepted_word_cases = 0
    nontrivial = 0
    total_local_accept = 0
    for case in range(args.cases):
        keys = tuple(rng.getrandbits(32) for _ in range(3))
        a = 0 if case == 0 else rng.getrandbits(32)
        b = 0 if case == 0 else rng.getrandbits(32)
        r, z = rng.getrandbits(32), rng.getrandbits(32)
        ctx = triple_word(*keys, a, b, r, z)
        check_word_trace(ctx)
        accepted_word_cases += int(ctx["accepted"])
        # A few sampled *honest boundary configurations*. No assertion
        # that their local row counts multiply to a true word count.
        if case < 32:
            row = probe_row(ctx, case % 8)
            rows.append(row)
            total_local_accept += row["accepted_assignments"]
            nontrivial += int(0 < row["accepted_assignments"] < 256)
    certified_positive_regressions = check_certified_five_round_positive_fixtures()
    report = {
        "certified_positive_regressions": certified_positive_regressions,
        "scope": "one-nibble exact 3-carry join with real boundary tags",
        "not_a_full_five_round_DDT_count": True,
        "seed": args.seed,
        "checked_full_word_cases": args.cases,
        "accepted_full_triples": accepted_word_cases,
        "sampled_local_rows": len(rows),
        "nontrivial_local_rows": nontrivial,
        "sampled_accepted_assignments": total_local_accept,
        "local_transition_options_per_row": 256,
        "naive_three_carry_bits": 6,
        "extra_delay_bits_for_rol11_two_tag_streams": 22,
        "naive_upper_bound_bits_before_constraints": 28,
        "sampled_rows": rows,
        "elapsed_seconds": round(time.monotonic()-started, 3),
        "proof_status": "Python regression vs full actual Magma g; Lean proved one-step and eight-step g reconstruction",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("TRIPLE_CARRY_ONE_NIBBLE_OK", json.dumps({
        k: v for k, v in report.items()
        if k not in ("sampled_rows", "certified_positive_regressions")
    }, sort_keys=True), flush=True)
    for result in certified_positive_regressions:
        print("LEAN_WITNESS_FIVE_ROUND_REGRESSION",json.dumps(result,sort_keys=True),flush=True)


if __name__ == "__main__":
    main()
