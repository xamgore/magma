#!/usr/bin/env python3
"""Exact branch-and-ROBDD model counting with safe resource caps.

For nonzero input XOR difference (0,a), pair (x,x XOR (0,a))
is counted twice in an ordinary DDT. Choose a toggled input bit,
fix it to zero, count each unordered pair once, and multiply by 2.
This is an exact bijection with no independence approximation.

Partition remaining base bits by a specified nibble: every branch is
disjoint, and integer counts are summed only if ALL branches complete.
The S-box is represented exactly in algebraic normal form (ANF).
The first 5-round tests use 4-/8-bit-word toys, NOT full RFC Magma.
"""
import argparse
import json
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
import overlap_j_circuit_bdd as circuit
from sbox_bdd_optimizer import anf_sbox
from two_word_bdd_probe import solve
from five_factor_sparse_regression import feistel_toy

def run(w,rot,a,b,indices,max_nodes=250000,max_seconds=5):
    assert len(indices)==4
    toggled=w+((a&-a).bit_length()-1)
    assert toggled not in indices
    start=time.monotonic()
    count=0
    done=0
    peak=0
    total=0
    for seed in range(16):
        fixed=dict(zip(indices,((seed>>i)&1 for i in range(4))))
        result=solve(w,(1,2,3,4,5),a,b,rot,"input","interleave",
                     max_nodes,max_seconds,fixed,canonical_pair=True)
        done+=1
        peak=max(peak,result["created_bdd_nodes"])
        total+=result["created_bdd_nodes"]
        if result["status"]!="complete":
            return dict(status="LIMIT",reason=result["reason"],
                        completed_branches=done-1,
                        peak_bdd_nodes=peak,
                        cumulative_bdd_nodes=total,
                        elapsed_s=round(time.monotonic()-start,3))
        count+=result["count"]
    return dict(status="complete",ddt=count,completed_branches=done,
                peak_bdd_nodes=peak,cumulative_bdd_nodes=total,
                elapsed_s=round(time.monotonic()-start,3))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--max-nodes",type=int,default=250000)
    p.add_argument("--seconds",type=int,default=5)
    args=p.parse_args()
    circuit.sbox_4=anf_sbox
    tests=[
        (4,1,8,4,(0,1,2,3),4),
        (8,3,1,215,(0,1,2,3),2),
        (8,3,1,215,(4,5,6,7),2),
        (8,3,1,215,(12,13,14,15),2),
        (12,7,1,121,(4,5,6,7),548),
    ]
    for w,rot,a,b,indices,expected in tests:
        r=run(w,rot,a,b,indices,args.max_nodes,args.seconds)
        if r["status"]=="complete":assert r["ddt"]==expected,(w,indices,r,expected)
        print("CANONICAL_BRANCH_BDD",json.dumps(dict(
            word_bits=w,alpha=a,beta=b,
            conditioning_bits=list(indices),expected_ddt=expected,
            **r),sort_keys=True),flush=True)
    print("CANONICAL_BRANCH_BDD_GATE_END",flush=True)

if __name__=="__main__":main()
