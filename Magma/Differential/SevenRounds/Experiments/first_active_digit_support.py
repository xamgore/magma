#!/usr/bin/env python3
"""Exact first-active S-box DIGIT support: sound key-free Magma g filter.

Input d nonzero: at its FIRST active input bit j=4*i+v,
the two values x+k and (x XOR d)+k differ in the SAME
first bit (2-adic valuation preserved). All lower complete
nibbles are identical. At nibble i, their XOR input digit
has lowest set bit v, but higher bits are unknown.
The resulting first nonzero S-box OUTPUT DIGIT must be in
  {S_i(u) XOR S_i(u XOR t): u in [0,15],
   t in [0,15] with lowbit(t) = 2^v}.
Thus the full 32-bit g output difference e must have
rotR11(e) low i nibbles zero, nibble i in this support
set, and higher digits arbitrary.

This is a rigorous KEY-UNIVERSAL necessary condition, not
an independent-DDT multiplication. SAT is only an abstract
difference witness; UNSAT would certify every-real-key zero.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json
import time
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX,g
from z3 import (
    BitVec,BitVecVal,Extract,RotateRight,And,Or,Solver,sat,unsat
)

MASK=(1<<32)-1
SUPPORT={}
for i,S in enumerate(BOX):
    for v in range(4):
        good={S[u]^S[u^t] for u in range(16) for t in range(1,16)
              if (t & -t)==(1<<v)}
        assert 0 not in good
        SUPPORT[(i,v)]=sorted(good)

def local_necessary(d,e):
    er=RotateRight(e,11)
    clauses=[And(d==BitVecVal(0,32), e==BitVecVal(0,32))]
    for i in range(8):
        for v in range(4):
            bit=4*i+v
            din=And(
                (d & BitVecVal((1<<bit)-1,32))==BitVecVal(0,32),
                (d & BitVecVal(1<<bit,32))!=BitVecVal(0,32))
            val=Extract(4*i+3,4*i,er)
            out=And(
                (er & BitVecVal((1<<(4*i))-1,32))==BitVecVal(0,32),
                Or(*[val==j for j in SUPPORT[(i,v)]]))
            clauses.append(And(din,out))
    return Or(*clauses)

def probe(core,i,j,timeout_ms=10000):
    # Entire 32-bit endpoints, upper input nibbles UNCONSTRAINED.
    a,b=BitVec('a',32),BitVec('b',32)
    d=[BitVecVal(0,32),a]+[BitVec('d'+str(t),32)
        for t in range(2,core)]+[b,BitVecVal(0,32)]
    assert len(d)==core+2
    s=Solver();s.set(timeout=timeout_ms)
    for t in range(core):
        s.add(local_necessary(d[t+1],d[t]^d[t+2]))
    from Magma.Differential.SevenRounds.Experiments.nibble_valuation_relaxation import low_nibble_pred
    s.add(low_nibble_pred(a,i),low_nibble_pred(b,j))
    start=time.monotonic()
    status=s.check()
    result=dict(core=core,outer=core+2,
        input_first_nibble=i,output_first_nibble=j,
        status=str(status),seconds=round(time.monotonic()-start,3))
    if status==sat:
        m=s.model()
        result['abstract_trace']=[f'0x{m.eval(v).as_long():08x}' for v in d]
    return result

def assert_real_g_sound(timeout_ms):
    """Negate the single-round rule against full 32-bit RFC g;
    arbitrary keys, base and difference remain symbolic."""
    from Magma.Differential.FiveRounds.Experiments.opposite_five_fiber import z3_g_library
    from z3 import Not
    key,x,d=(BitVec(name,32) for name in
             ('all_key','all_base','all_difference'))
    g=z3_g_library()
    s=Solver()
    s.set(timeout=timeout_ms)
    s.add(Not(local_necessary(d,g(key,x^d)^g(key,x))))
    started=time.monotonic()
    status=s.check()
    print('UNIVERSAL_FIRST_DIGIT_RFC_G_SOUNDNESS',
          json.dumps(dict(status=str(status),
                          elapsed_s=round(time.monotonic()-started,3),
                          full32=True,all_keys=True,all_bases=True),
                     sort_keys=True),flush=True)
    assert status==unsat, 'full-32-digit-filter soundness NOT certified'

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--timeout-ms',type=int,default=15000)
    parser.add_argument('--full-grid',action='store_true')
    parser.add_argument('--check-real-g',action='store_true')
    args=parser.parse_args()
    if args.check_real_g: assert_real_g_sound(args.timeout_ms)
    print('LOCAL_KEYFREE_FIRST_DIGIT_SUPPORT',
        json.dumps([{'nibble':i,'first_bit':v,'output_nibble':SUPPORT[i,v]}
                    for i in range(8) for v in range(4)],sort_keys=True),flush=True)
    tests=[(5,7,7),(7,7,7),(7,6,6),(7,6,7),
           (7,7,6),(7,5,6),(7,6,5),(6,7,7)]
    if args.full_grid:
        tests=[(core,i,j) for core in (5,6,7)
               for i in range(8) for j in range(8)]
    results=[]
    for core,i,j in tests:
        r=probe(core,i,j,args.timeout_ms)
        results.append(r)
        print('KEYFREE_FIRST_DIGIT',json.dumps(r,sort_keys=True),flush=True)
    if args.full_grid:
        assert all(r['status'] in ('sat','unsat') for r in results), \
            'UNKNOWN must never be promoted to a zero'
        expected={(5,5,6),(5,6,5),(5,6,6),
                  (5,6,7),(5,7,6),(5,7,7)}
        actual={(r['core'],r['input_first_nibble'],r['output_first_nibble'])
                for r in results if r['status']=='unsat'}
        assert actual==expected,(actual,expected)
        print('FIRST_DIGIT_FULL_GRID_GATE_OK',
              json.dumps(dict(total=len(results),
                              proven_rejections=len(actual),
                              core_7_rejections=0,
                              status='complete'),sort_keys=True),flush=True)

if __name__=='__main__':main()
