#!/usr/bin/env python3
"""Bounded four-round reflected Z3 pair-counting probe.

For the 9-round palindrome [u,v,w,z,z,w,v,u,tail]:
  D9((a,0),(0,b)) = #{(x,y):
      H(y)=J H(x),
      H(y XOR (0,b))=J H(x XOR (a,0))}.
Here H consists of four real key-linked ordinary Feistel
rounds. The first condition ensures UNIQUE y for each x.
NO independent 4-round DDT factors. Exact counts are returned
ONLY after model enumeration reaches UNSAT; cap/timeout is LIMIT.
Runs on 4/8-bit authentic-Sbox toys and optional 32-bit RFC
Magma (the latter may reach LIMIT). Every SAT model is replayed
with an independent integer Feistel implementation.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse,json,sys,time
from pathlib import Path
DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy
from Magma.Differential.FiveRounds.Experiments.opposite_five_fiber import z3_g_library
from z3 import (BitVec,BitVecVal,Extract,Concat,ZeroExt,LShR,
    RotateLeft,Solver,Or,sat,unsat)

from Magma.Differential.FiveRounds.Experiments.five_factor_sparse import BOX
LOOKUP=[sum(int(v) << (4*j) for j,v in enumerate(box)) for box in BOX]

G32=z3_g_library()

def sym_g(k,x,width,rot):
    if width==32:
        return G32(k,x)
    t=k+x
    digits=[Extract(3,0,LShR(BitVecVal(LOOKUP[i],64),
               ZeroExt(60,Extract(4*i+3,4*i,t))<<2))
            for i in reversed(range(width//4))]
    sub=digits[0] if len(digits)==1 else Concat(*digits)
    return RotateLeft(sub,rot)

def sym_chain(keys,x,width,rot):
    l,r=x
    for key in keys:
        l,r=r,l^sym_g(BitVecVal(key,width),r,width,rot)
    return l,r

def real_chain(keys,x,width,rot):
    if width<=16:
        return feistel_toy(keys,x[0],x[1],width//4,rot)
    from Magma.Differential.Windows.Experiments.SAT.verify_nround import g
    l,r=x
    for key in keys:
        l,r=r,l^g(key,r)
    return l,r

def solve(w,rotation,keys,a,b,method,timeout_ms,max_models):
    assert len(keys)==4 and a!=0 and b!=0
    start=time.monotonic()
    first4=tuple(keys)
    nine=tuple(keys)+tuple(reversed(keys))+(0,)
    L,R=BitVec('base_L',w),BitVec('base_R',w)
    s=Solver();s.set(timeout=timeout_ms)
    if method=='cross4':
        YL,YR=BitVec('partner_L',w),BitVec('partner_R',w)
        u=sym_chain(first4,(L,R),w,rotation)
        v=sym_chain(first4,(YL,YR),w,rotation)
        up=sym_chain(first4,(L^BitVecVal(a,w),R),w,rotation)
        vp=sym_chain(first4,(YL,YR^BitVecVal(b,w)),w,rotation)
        s.add(v[0]==u[1],v[1]==u[0])
        s.add(vp[0]==up[1],vp[1]==up[0])
        vars=(L,R,YL,YR)
    elif method=='direct9':
        z=sym_chain(nine,(L,R),w,rotation)
        zp=sym_chain(nine,(L^BitVecVal(a,w),R),w,rotation)
        s.add((z[0]^zp[0])==BitVecVal(0,w),
              (z[1]^zp[1])==BitVecVal(b,w))
        vars=(L,R)
    else:raise ValueError(method)
    count=0
    witnesses=[]
    state='unknown'
    while count<max_models:
        status=s.check()
        if status==unsat:
            state='complete'
            break
        if status!=sat:
            state='LIMIT_UNKNOWN'
            break
        m=s.model()
        vals=tuple(m.eval(var).as_long() for var in vars)
        x=vals[:2]
        out=real_chain(nine,x,w,rotation)
        outp=real_chain(nine,(x[0]^a,x[1]),w,rotation)
        assert (out[0]^outp[0],out[1]^outp[1])==(0,b),(method,w,vals)
        if method=='cross4':
            y=vals[2:]
            assert real_chain(first4,y,w,rotation)==tuple(reversed(
                       real_chain(first4,x,w,rotation)))
            assert real_chain(first4,(y[0],y[1]^b),w,rotation)==tuple(
                reversed(real_chain(first4,(x[0]^a,x[1]),w,rotation)))
        if len(witnesses)<3:witnesses.append([hex(v) for v in vals])
        count+=1
        s.add(Or(*[var!=BitVecVal(v,w) for var,v in zip(vars,vals)]))
    if count==max_models:
        if s.check()==unsat:state='complete'
        else:state='LIMIT_MODELS'
    result=dict(scope=('32-bit true RFC Magma' if w==32
                       else f'{w}-bit authentic-Sbox toy'),
        method=method,word_bits=w,first4=[hex(k) for k in keys],
        alpha=hex(a),beta=hex(b),status=state,
        count_or_lower_bound=count if state=='complete' else None,
        enumerated_witnesses=count,
        example_bases=witnesses,
        seconds=round(time.monotonic()-start,3),
        check='every satisfying model independently replayed')
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--seconds',type=int,default=5)
    parser.add_argument('--max-models',type=int,default=600)
    parser.add_argument('--full32',action='store_true')
    args=parser.parse_args()
    cases=[
        (4,1,(5,6,7,8),1,1),
        (4,1,(5,6,7,8),8,4),
        (4,1,(1,2,3,4),8,7),
        (8,3,(1,2,3,4),1,0xd7),
    ]
    if args.full32:
        cases=[(32,11,(0,0x2056,0xfdfa7789,0xf0f8d960),
                0x80000000,0x80000000)]
    for w,rot,keys,a,b in cases:
        rows=[]
        for method in ('cross4','direct9'):
            row=solve(w,rot,keys,a,b,method,
                      args.seconds*1000,args.max_models)
            rows.append(row)
            print('REFLECTED_CROSS4_TEST',
                  json.dumps(row,sort_keys=True),flush=True)
        if all(r['status']=='complete' for r in rows):
            assert rows[0]['count_or_lower_bound']==rows[1]['count_or_lower_bound']
            print('REFLECTED_CROSS4_EXACT_EQUALITY_PASS',w,hex(a),hex(b),flush=True)
        else:
            print('REFLECTED_CROSS4_BOUNDED_NO_COUNT_CLAIM',w,hex(a),hex(b),flush=True)

if __name__=='__main__':main()
