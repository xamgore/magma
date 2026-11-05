#!/usr/bin/env python3
"""Exact 32-bit Magma three-carry fiber sum over a small middle-word subcube.

The fixed-h weighted transfer is run for all 2^bits low-bit
variants of h, holding the other 32-bits fixed. Independently,
Z3 counts all (r,z) solutions with only the same HIGH h bits
constrained. Exhaustion to UNSAT confirms exact aggregation.

This is a real full-width fixed-key Magma computation. It remains a
restricted slice of the FULL five-round DDT and is NOT a 9-round ID.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json
import time
from pathlib import Path

from Magma.Differential.FiveRounds.Experiments.fixed_middle_transfer import (
    conditional_count, known_positive_fixtures, witness_fiber
)

ROOT=Path(__file__).resolve().parents[4]
MASK=(1<<32)-1


def z3_enumerate_subcube(k1,k2,k3,a,b,base,bits,expected,
                         timeout_ms=20000,cap=600):
    from z3 import BitVec, BitVecVal, Concat, Extract, LShR
    from z3 import RotateLeft, Solver, ZeroExt, sat, unsat, Or
    from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX

    lookup=[sum(int(v) << (4*j) for j,v in enumerate(box)) for box in BOX]
    def G(k,x):
        v=k+x
        out=Concat(*[
            Extract(3,0,LShR(BitVecVal(lookup[i],64),
               ZeroExt(60,Extract(4*i+3,4*i,v)) << 2))
            for i in range(7,-1,-1)
        ])
        return RotateLeft(out,11)

    R,Z=BitVec('all_r',32),BitVec('all_z',32)
    K1,K2,K3=[BitVecVal(v,32) for v in (k1,k2,k3)]
    A,B=[BitVecVal(v,32) for v in (a,b)]
    H=G(K2,Z)
    c=G(K1,R^A)^G(K1,R)
    mask=MASK^((1<<bits)-1)
    s=Solver()
    s.set(timeout=timeout_ms)
    s.add((H & BitVecVal(mask,32))==BitVecVal(base&mask,32))
    s.add((G(K2,Z^c)^G(K2,Z))==A^B)
    s.add((G(K3,(R^H)^B)^G(K3,R^H))==c)
    count=0
    started=time.monotonic()
    while count<=expected and count<cap:
        check=s.check()
        if check==unsat:
            assert count==expected,(count,expected)
            return dict(status='exact_verified_by_independent_Z3',
                        count=count,
                        seconds=round(time.monotonic()-started,3))
        if check!=sat:
            return dict(status='unknown',lower_bound=count,
                        seconds=round(time.monotonic()-started,3))
        model=s.model()
        rr=model.eval(R).as_long()
        zz=model.eval(Z).as_long()
        s.add(Or(R!=BitVecVal(rr,32),Z!=BitVecVal(zz,32)))
        count+=1
    if count>expected:
        raise AssertionError(f'Z3 found more solutions than DP: {count}>{expected}')
    return dict(status='model_cap',lower_bound=count,
                seconds=round(time.monotonic()-started,3))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--fixture',type=int,choices=(0,1),default=0)
    ap.add_argument('--subcube-bits',type=int,default=4,choices=(1,2,3,4,5,6,7,8))
    ap.add_argument('--z3-timeout-ms',type=int,default=20000)
    ap.add_argument('--z3-model-cap',type=int,default=600)
    ap.add_argument('--output',type=Path)
    cfg=ap.parse_args()
    fixture=known_positive_fixtures()[cfg.fixture]
    k1,k2,k3,a,b,h,r,z=witness_fiber(fixture)
    mask=MASK^((1<<cfg.subcube_bits)-1)
    hi=h&mask
    start=time.monotonic()
    counts=[]
    max_frontier=0
    accepted_edges=0
    for low in range(1<<cfg.subcube_bits):
        hword=hi|low
        count,stat=conditional_count(k1,k2,k3,a,b,hword)
        counts.append(count)
        max_frontier=max(max_frontier,stat['max_frontier'])
        accepted_edges+=stat['accepted_local_edges']
    total=sum(counts)
    dp_seconds=round(time.monotonic()-start,3)
    z3=z3_enumerate_subcube(k1,k2,k3,a,b,hi,cfg.subcube_bits,
                           total,cfg.z3_timeout_ms,cfg.z3_model_cap)
    report=dict(
      fixture=fixture['name'],
      full_width_32_bit_Magma=True,
      key_words=[f'0x{k:08x}' for k in (k1,k2,k3)],
      alpha=f'0x{a:08x}',sigma=f'0x{b:08x}',
      fixed_middle_h_high=f'0x{hi:08x}',
      free_middle_h_low_bits=cfg.subcube_bits,
      middle_h_words=1<<cfg.subcube_bits,
      exact_fixed_h_counts=counts,
      exact_weighted_subcube_sum=total,
      maximum_observed_frontier=max_frontier,
      total_accepted_local_edges=accepted_edges,
      dp_seconds=dp_seconds,
      independent_z3_enumeration=z3,
      limitation='restricted middle h subcube; NOT total five-round DDT',
      proof_status='Python exact weighted DP and independent #SMT where completed',
    )
    output=cfg.output or ROOT/f'Magma/Differential/FiveRounds/Experiments/fixed_middle_subcube_{cfg.fixture}.json'
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+'\n')
    print('SUBCUBE_32BIT_MAGMA_EXACT',json.dumps({
        k:v for k,v in report.items() if k!='exact_fixed_h_counts'
    },sort_keys=True),flush=True)


if __name__=='__main__':
    main()
