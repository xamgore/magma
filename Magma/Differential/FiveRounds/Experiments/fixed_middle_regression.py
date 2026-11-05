#!/usr/bin/env python3
"""Deterministic cross-checks of the exact full-width FIXED-h carry DP.

Verifies known actual five-round Magma witnesses, full 2^32 zero
multiplicities, and a random collection of nearby/independent middle
words. Small fiber counts are cross-checked by independent Z3 model
enumeration where feasible. Unsolved Z3 checks remain UNKNOWN.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json
import random
import time
from pathlib import Path

from Magma.Differential.FiveRounds.Experiments.fixed_middle_transfer import (
    conditional_count, known_positive_fixtures, witness_fiber,
    z3_enumerate_conditional
)

ROOT = Path(__file__).resolve().parents[4]


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--samples-per-fixture", type=int, default=64)
    p.add_argument("--seed", type=int, default=8891)
    p.add_argument("--z3-checks-per-fixture", type=int, default=6)
    p.add_argument("--z3-timeout-ms", type=int, default=12000)
    p.add_argument("--output", type=Path,
                   default=ROOT / "Magma/Differential/FiveRounds/Experiments/fixed_middle_regression.json")
    cfg = p.parse_args()
    assert 1 <= cfg.samples_per_fixture <= 4096
    assert 0 <= cfg.z3_checks_per_fixture <= cfg.samples_per_fixture
    rng = random.Random(cfg.seed)
    started = time.monotonic()
    fixtures = []
    for fixture_id, fixture in enumerate(known_positive_fixtures()):
        k1, k2, k3, a, b, original_h, actual_r, z = witness_fiber(fixture)
        original_count, original_stat = conditional_count(
            k1, k2, k3, a, b, original_h)
        assert original_count > 0
        independent = z3_enumerate_conditional(
            k1, k2, k3, a, b, original_h, original_count,
            cfg.z3_timeout_ms)
        assert independent["status"] == "exact_verified_by_independent_Z3"
        assert independent["count"] == original_count

        zero_count, zero_stat = conditional_count(k1, k2, k3, 0, 0, original_h)
        assert zero_count == 2**32

        sample_words = []
        for j in range(cfg.samples_per_fixture):
            if j < 32:
                h = original_h ^ (1 << j)
            else:
                h = rng.getrandbits(32)
            assert h != original_h
            sample_words.append(h)
        rows = []
        sampled_positive = 0
        max_frontier = 0
        max_count = 0
        independent_checked = 0
        for j, h in enumerate(sample_words):
            count, stat = conditional_count(k1, k2, k3, a, b, h)
            sampled_positive += int(count > 0)
            max_frontier = max(max_frontier, stat["max_frontier"])
            max_count = max(max_count, count)
            row = {
                "middle_h": f"0x{h:08x}",
                "exact_count": count,
                "max_frontier": stat["max_frontier"],
                "seconds": stat["seconds"],
            }
            if j < cfg.z3_checks_per_fixture:
                check = z3_enumerate_conditional(
                    k1, k2, k3, a, b, h, count, cfg.z3_timeout_ms)
                row["z3_check"] = check
                if check["status"] == "exact_verified_by_independent_Z3":
                    independent_checked += 1
            rows.append(row)
        result = {
            "name": fixture["name"],
            "witness_middle_h": f"0x{original_h:08x}",
            "witness_r": f"0x{actual_r:08x}",
            "exact_count_at_witness_h": original_count,
            "witness_z3_check": independent,
            "zero_difference_count_at_same_h": zero_count,
            "zero_difference_max_frontier": zero_stat["max_frontier"],
            "sampled_middle_h": cfg.samples_per_fixture,
            "sampled_positive_fibers": sampled_positive,
            "sampled_zero_fibers": cfg.samples_per_fixture - sampled_positive,
            "sampled_max_count": max_count,
            "sampled_max_frontier": max_frontier,
            "sampled_independent_Z3_exact_checks": independent_checked,
            "sampled_rows": rows,
        }
        fixtures.append(result)
        print("FULLWIDTH_FIXED_H_REGRESSION", json.dumps({
            k:v for k,v in result.items() if k != "sampled_rows"
        }, sort_keys=True),flush=True)
    report = {
        "seed":cfg.seed,
        "scope":"fixed 32-bit Magma middle word; NOT total DDT",
        "samples_per_fixture":cfg.samples_per_fixture,
        "repeated_positive_witnesses":2,
        "elapsed_seconds":round(time.monotonic()-started,3),
        "proof_status":"Python weighted transfer and independent Z3 checks, not Lean-certified total DP",
        "fixtures":fixtures,
    }
    cfg.output.parent.mkdir(parents=True, exist_ok=True)
    cfg.output.write_text(json.dumps(report,indent=2)+"\n")
    print("FULLWIDTH_CONDITIONAL_FIBER_REGRESSION_OK",
          len(fixtures), "fixtures",report["elapsed_seconds"],"seconds",flush=True)


if __name__=="__main__":
    main()
