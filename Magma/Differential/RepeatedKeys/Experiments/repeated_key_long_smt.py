#!/usr/bin/env python3
"""True RFC 32-bit g, scheduled *ordinary* Feistel G, short-key recovery SMT.

User's exact patterns: ABCABC and ABABBA.
Control true palindrome: ABAABA (the user called ABABBA symmetric,
but reversing ABABBA gives ABBABA, NOT ABABBA).

Every named key is one independent 32-bit word; all occurrences
SHARE the very same Z3 bitvector. All 8 RFC Sboxes and modular carries
and ROL11 are real. Fixed unknown key; 2/3 known (selected) input/output
pairs. GStar swaps final output halves; this experiment uses ordinary G
and does not claim to have attacked full 32-round native RFC.

SAT means found some correctly-replayed key; does NOT assert uniqueness
unless the optional blocking solver returned unsat.
UNKNOWN means solver budget exhausted, NOT any lower bound.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json
import random
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX,g as g_reference
import z3

MASK=(1<<32)-1

def ordinary(keys,L,R):
    for k in keys:
        L,R=R,L^g_reference(k,R)
    return L,R

ARRAYS=[]
for box in BOX:
    arr=z3.K(z3.BitVecSort(4),z3.BitVecVal(0,4))
    for i,v in enumerate(box):
        arr=z3.Store(arr,z3.BitVecVal(i,4),z3.BitVecVal(v,4))
    ARRAYS.append(arr)

def z3_g(k,x):
    z=x+k
    t=z3.Concat(*[z3.Select(ARRAYS[i], z3.Extract(i*4+3,i*4,z))
                    for i in range(7,-1,-1)])
    return z3.RotateLeft(t,11)

def symbolic(keyvars, pattern,L,R):
    for name in pattern:
        L,R=R,L^z3_g(keyvars[name],R)
    return L,R

def check_one(pattern,pairs,seed,limit,unique_ms=0,verbose=False):
    letters=tuple(sorted(set(pattern)))
    assert 2<=len(letters)<=3,letters
    rng=random.Random(seed)
    secret={c:rng.getrandbits(32) for c in letters}
    inputs=[]
    for _ in range(pairs):
        L,R=rng.getrandbits(32),rng.getrandbits(32)
        U,V=ordinary([secret[c] for c in pattern],L,R)
        inputs.append((L,R,U,V))
    keys={c:z3.BitVec('guess_'+c,32) for c in letters}
    solver=z3.Solver()
    solver.set(timeout=limit)
    start=time.monotonic()
    for L,R,U,V in inputs:
        lhs,rhs=symbolic(keys,pattern,z3.BitVecVal(L,32),z3.BitVecVal(R,32))
        solver.add(lhs==z3.BitVecVal(U,32),rhs==z3.BitVecVal(V,32))
    encoded=time.monotonic()-start
    if verbose:
        print('START',json.dumps({
            'pattern':pattern,'pairs':pairs,'seed':seed,
            'key_bits':32*len(letters),'timeout_ms':limit,
            'encoding_seconds':round(encoded,3),
            'number_of_assertions':len(solver.assertions())}),flush=True)
    ts=time.monotonic()
    result=solver.check()
    solve_time=time.monotonic()-ts
    report=dict(
        pattern=pattern,rounds=len(pattern),pairs=pairs,seed=seed,
        known_key_words=len(letters),unknown_key_bits=32*len(letters),
        status=str(result),timeout_ms=limit,
        encoding_seconds=round(encoded,3),
        solver_seconds=round(solve_time,3),
        full_wall_seconds=round(time.monotonic()-start,3))
    if result==z3.sat:
        guess={c:solver.model().eval(keys[c]).as_long() for c in letters}
        same=guess==secret
        valid=all(ordinary([guess[c] for c in pattern],L,R)==(U,V)
                    for L,R,U,V in inputs)
        assert valid,'SAT solver model MUST reproduce real ciphertexts'
        report.update(model_is_correct_key=same,
                      independent_replay=True,
                      recovered_key_words_hex={c:hex(guess[c]) for c in letters})
        if unique_ms:
            solver.add(z3.Or(*[keys[c]!=z3.BitVecVal(guess[c],32) for c in letters]))
            solver.set(timeout=unique_ms)
            tut=time.monotonic()
            more=solver.check()
            report.update(
                uniqueness_second_model_status=str(more),
                uniqueness_check_seconds=round(time.monotonic()-tut,3),
                unique_key_proven=(more==z3.unsat))
            if more==z3.sat:
                second={c:solver.model().eval(keys[c]).as_long() for c in letters}
                assert all(ordinary([second[c] for c in pattern],L,R)==(U,V)
                           for L,R,U,V in inputs)
                report['distinct_second_key_replayed']=True
    elif result==z3.unsat:
        raise AssertionError("Generated genuine key MUST satisfy full model")
    else:
        report["reason_unknown"]=solver.reason_unknown()
    return report

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--pattern',required=True)
    p.add_argument('--pairs',type=int,default=2)
    p.add_argument('--seed',type=int,default=4106)
    p.add_argument('--timeout',type=int,default=600000)
    p.add_argument('--uniqueness-timeout',type=int,default=0)
    args=p.parse_args()
    assert len(args.pattern)>=3
    assert all(c in "ABC" for c in args.pattern)
    out=check_one(args.pattern,args.pairs,args.seed,args.timeout,
                  args.uniqueness_timeout,verbose=True)
    print("REPEATED_FULLWORD_MIXED_SMT",json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
