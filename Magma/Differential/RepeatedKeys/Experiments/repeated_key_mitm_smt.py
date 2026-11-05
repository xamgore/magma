#!/usr/bin/env python3
"""Bidirectional meet-in-the-middle SMT with repeated genuine RFC g words.

All hidden intermediate states are eliminated by equality of *symbolic*
three-round prefix and three-round inverse suffix at same midpoint.
For G_k(L,R)=(R,L xor g_k(R)), inverse G_k^-1(U,V)=(V xor g_k(U),U).

This is exact bitvector SAT for given observed input/output pairs;
not a classical time-memory exhaustive MITM and not a full RFC break.
Compare ANF (bitwise Sbox polynomials) versus array Store/Select.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse,json,random,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]

import Magma.Differential.RepeatedKeys.Experiments.repeated_key_long_smt as base
import Magma.Differential.RepeatedKeys.Experiments.repeated_key_anf_smt as anf
z3=base.z3

def g_f(k,x,encoding):
    return anf.anf_g(k,x) if encoding=='anf' else base.z3_g(k,x)

def forward(L,R,seq,keys,enc):
    for n in seq:
        L,R=R,L^g_f(keys[n],R,enc)
    return L,R

def backward(U,V,seq,keys,enc):
    for n in reversed(seq):
        U,V=V^g_f(keys[n],U,enc),U
    return U,V

def probe(pattern,pairs,seed,timeout,encoding,unique,input_mode='random'):
    keynames=tuple(sorted(set(pattern)))
    rng=random.Random(seed)
    secret={c:rng.getrandbits(32) for c in keynames}
    obs=[]
    fixed_right=(0 if input_mode=='zero-right' else rng.getrandbits(32)) if input_mode!='random' else None
    for _ in range(pairs):
        L,R=rng.getrandbits(32),(rng.getrandbits(32) if fixed_right is None else fixed_right)
        U,V=base.ordinary([secret[c] for c in pattern],L,R)
        obs.append((L,R,U,V))
    unknowns={c:z3.BitVec('key_'+c,32) for c in keynames}
    m=len(pattern)//2
    solver=z3.Solver()
    solver.set(timeout=timeout)
    for L,R,U,V in obs:
        fp=forward(z3.BitVecVal(L,32),z3.BitVecVal(R,32),
                   pattern[:m],unknowns,encoding)
        bp=backward(z3.BitVecVal(U,32),z3.BitVecVal(V,32),
                    pattern[m:],unknowns,encoding)
        solver.add(fp[0]==bp[0],fp[1]==bp[1])
    ts=time.monotonic()
    status=solver.check()
    elapsed=time.monotonic()-ts
    result=dict(pattern=pattern,pairs=pairs,seed=seed,
        key_bits=32*len(keynames),backend=encoding,
        constraint_type="bidirectional_midpoint_equality",
        input_mode=input_mode,
        solver_seconds=round(elapsed,3),timeout_ms=timeout,
        status=str(status))
    if status==z3.sat:
        guessed={c:solver.model().eval(unknowns[c]).as_long() for c in keynames}
        matches=all(base.ordinary([guessed[c] for c in pattern],L,R)==(U,V)
                    for L,R,U,V in obs)
        assert matches
        result['found_actual_key']=guessed==secret
        result['independent_oracle_replay']=True
        result['key_hex']={c:hex(guessed[c]) for c in keynames}
        if unique:
            solver.add(z3.Or(*[unknowns[c]!=z3.BitVecVal(guessed[c],32) for c in keynames]))
            solver.set(timeout=unique)
            t=time.monotonic();r=solver.check()
            result['distinct_key_check']=str(r)
            result['distinct_key_seconds']=round(time.monotonic()-t,3)
    elif status==z3.unsat:
        raise AssertionError('real secret must satisfy equations')
    else:
        result['reason']=solver.reason_unknown()
    return result

def main():
    a=argparse.ArgumentParser()
    a.add_argument('--pattern',required=True)
    a.add_argument('--pairs',type=int,default=2)
    a.add_argument('--seed',type=int,default=4106)
    a.add_argument('--timeout',type=int,default=600000)
    a.add_argument('--encoding',choices=('anf','array'),default='anf')
    a.add_argument('--uniqueness-timeout',type=int,default=0)
    a.add_argument('--input-mode',choices=('random','same-right','zero-right'),default='random')
    args=a.parse_args()
    assert all(c in 'ABC' for c in args.pattern)
    st=time.monotonic()
    print('START_MITM',json.dumps(vars(args),sort_keys=True),flush=True)
    out=probe(args.pattern,args.pairs,args.seed,args.timeout,args.encoding,args.uniqueness_timeout,args.input_mode)
    out['full_wall_seconds']=round(time.monotonic()-st,3)
    print('REPEATED_KEY_MITM_SMT',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
