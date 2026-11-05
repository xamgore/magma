#!/usr/bin/env python3
"""Deterministic five-chain carry/tag semantics and factor-width regression.

Checks four exact fixed-key opposite-oriented fibers (including an 8-pair
control with nonzero outer keys), against a structurally DIFFERENT
middle-word #SMT oracle and independently replayed real RFC rounds.
Width results are structural graph estimates, not measured DP frontiers.
No Rust exact five-chain weighted transfer is claimed.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import time
from Magma.Differential.FiveRounds.Experiments.five_factor_bit_width import bit_network
from Magma.Differential.FiveRounds.Experiments.five_factor_width import eliminate
from Magma.Differential.FiveRounds.Experiments.opposite_five_fiber import enumerate_core
from Magma.Differential.FiveRounds.Experiments.opposite_five_tagged import count_tagged

K=(0,0x2056,0xfdfa7789,0xf0f8d960,0)
K_ALT=(0x12345678,0x2056,0xfdfa7789,0xf0f8d960,0x87654321)
CASES=(
    ("positive",K,0x80000000,0x681e60a7,2),
    ("unit_zero",K,1,1,0),
    ("strict_zero",K,0x80000000,0x681e60a6,0),
    ("nonzero_outer_keys",K_ALT,0x80000000,0x1d43093d,8),
)

def main():
    t0=time.monotonic()
    result=[]
    for name,keys,a,b,count in CASES:
        tagged=count_tagged(keys,a,b,timeout_ms=15000,model_cap=100)
        direct=enumerate_core(keys,a,b,"middle",15000,100)
        assert tagged["status"]=="complete_unsat_after_enumeration",tagged
        assert direct["status"]=="complete_unsat_after_enumeration",direct
        assert tagged["count_or_lower_bound"]==direct["count_or_lower_bound"]==count
        assert tagged["sha256_sorted_middle_bases"]==direct["sha256_sorted_middle_bases"]
        result.append(dict(case=name,exact_ddt=count,
                           tagged_seconds=tagged["seconds"],
                           middle_seconds=direct["seconds"],
                           solution_hash=tagged["sha256_sorted_middle_bases"]))
        print("FIVE_TAGGED_EXACT_MATCH",name,count,flush=True)

    # Full heuristic estimate, not a lower bound: bit-splitting the delayed
    # rotate tags is necessary to avoid a useless whole-nibble clique.
    widths,factors,simple=bit_network(0x80000000,0x681e60a7,0)
    assert simple
    width=eliminate(widths,factors,"min-fill")
    print("FIVE_TAGGED_GRAPH_WIDTH",json.dumps(dict(
        variables=len(widths),factors=len(factors),**width),sort_keys=True),flush=True)
    assert width["peak_scope_bits"] < 150, "bit-level simplification lost"
    result.append(dict(graph_peak_bits_heuristic=width["peak_scope_bits"],
                       graph_peak_variables=width["peak_scope_variables"],
                       note="dense-factor scope proxy only; NOT actual sparse frontier"))
    print("FIVE_TAGGED_GATE_OK",json.dumps(dict(cases=result,
                            elapsed_seconds=round(time.monotonic()-t0,3))),flush=True)

if __name__=="__main__":
    main()
