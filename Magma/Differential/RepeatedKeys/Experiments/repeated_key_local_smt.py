#!/usr/bin/env python3
"""Exact per-round local (Tseitin) bitvector constraints for repeated keys.

State sequence x_-1=L, x_0=R, x_(j+1)=x_(j-1) XOR g_{k_j}(x_j);
ciphertext after n ordinary G rounds is (x_{n-1},x_n).

All x_i are independent existential Z3 32-bit variables,
rather than nested g expressions. Every key-name occurrence
is the SAME shared unknown 32-bit word, across all pairs.
This avoids treating marginal DDT rounds as independent.

Research-only, true RFC g, no full-32 Magma attack claim.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse,json,random,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import Magma.Differential.RepeatedKeys.Experiments.repeated_key_long_smt as base
import Magma.Differential.RepeatedKeys.Experiments.repeated_key_anf_smt as anf
z3=base.z3

def constraints(solver,pattern,unknowns,L,R,U,V,pair_index,encoding):
    n=len(pattern)
    states={-1:z3.BitVecVal(L,32),0:z3.BitVecVal(R,32),
            n-1:z3.BitVecVal(U,32),n:z3.BitVecVal(V,32)}
    for i in range(1,n-1):
        states[i]=z3.BitVec(f'mid_{pair_index}_{i}',32)
    gf=anf.anf_g if encoding=='anf' else base.z3_g
    for j,key_name in enumerate(pattern):
        solver.add(states[j+1] == states[j-1] ^ gf(unknowns[key_name],states[j]))
    return states

def probe(pattern,pairs,seed,timeout,encoding,mode,uniqueness=0):
    rng=random.Random(seed);keys=tuple(sorted(set(pattern)))
    secret={c:rng.getrandbits(32) for c in keys}
    obs=[];fixed_R=None if mode=='random' else (0 if mode=='zero-right' else rng.getrandbits(32))
    for _ in range(pairs):
        L,R=rng.getrandbits(32),rng.getrandbits(32) if fixed_R is None else fixed_R
        U,V=base.ordinary([secret[c] for c in pattern],L,R)
        obs.append((L,R,U,V))
    kvars={c:z3.BitVec('key_'+c,32) for c in keys}
    s=z3.Solver();s.set(timeout=timeout)
    t=time.monotonic()
    for i,(L,R,U,V) in enumerate(obs):
        constraints(s,pattern,kvars,L,R,U,V,i,encoding)
    encoding_seconds=round(time.monotonic()-t,3)
    t=time.monotonic();r=s.check()
    result=dict(pattern=pattern,pairs=pairs,seed=seed,mode=mode,
        unknown_key_bits=len(keys)*32,encoding=encoding,
        solver_strategy="local_intermediate_state_relation",
        solver_seconds=round(time.monotonic()-t,3),
        encoding_seconds=encoding_seconds,limit_ms=timeout,status=str(r))
    if r==z3.sat:
        guess={c:s.model().eval(kvars[c]).as_long() for c in keys}
        assert all(base.ordinary([guess[c] for c in pattern],L,R)==(U,V)
                   for L,R,U,V in obs)
        result['correct_key']=guess==secret
        result['independent_replay']=True
        result['keys_hex']={c:hex(v) for c,v in guess.items()}
        if uniqueness:
            s.add(z3.Or(*[kvars[c]!=z3.BitVecVal(guess[c],32) for c in keys]))
            s.set(timeout=uniqueness)
            t=time.monotonic();r2=s.check()
            result['uniqueness_status']=str(r2)
            result['uniqueness_seconds']=round(time.monotonic()-t,3)
    elif r==z3.unsat:
        raise AssertionError('Real key must satisfy the true cipher model')
    else:
        result['reason']=s.reason_unknown()
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--pattern',required=True)
    p.add_argument('--pairs',type=int,default=2)
    p.add_argument('--seed',type=int,default=4106)
    p.add_argument('--timeout',type=int,default=600000)
    p.add_argument('--encoding',choices=('anf','array'),default='anf')
    p.add_argument('--input-mode',choices=('random','zero-right','same-right'),default='random')
    p.add_argument('--uniqueness-timeout',type=int,default=0)
    a=p.parse_args()
    print('LOCAL_START',json.dumps(vars(a),sort_keys=True),flush=True)
    d=probe(a.pattern,a.pairs,a.seed,a.timeout,a.encoding,a.input_mode,a.uniqueness_timeout)
    print('REPEATED_LOCAL_SMT',json.dumps(d,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
