#!/usr/bin/env python3
"""Proof of concept: *symbolic* exact composition of two lifted 3-round J.

The toy has 4-bit Feistel words, hence 8-bit complete state u, 8-bit
difference delta and 8-bit common-round output difference gamma.
A reduced ordered binary decision diagram (ROBDD) stores both lifted
three-round relations over *all 24 bits*, with no lossy projection.
Conjunction and model counting recover exact five-round DDT values.

This is a toy-only proof of concept; it is NOT full-width Magma carryDP.
No SMT or independent-state multiplication is used to count paths.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import functools
import json
import time
from collections import defaultdict

from Magma.Differential.Reflection.Experiments.overlap_two_j_probe import (
    N, KEYS, decode, encode, fw, inv, xor, differential, ddt
)

class Limit(Exception):
    pass

class BDD:
    def __init__(self,order,max_nodes):
        self.order=order
        self.max_nodes=max_nodes
        self.unique={}
        self.nodes={0:None,1:None}
        self.nextid=2
        self.apply_cache={}
        self.max_apply_cache=0

    def node(self,level,lo,hi):
        if lo==hi:return lo
        key=(level,lo,hi)
        if key in self.unique:return self.unique[key]
        if self.nextid>self.max_nodes:raise Limit("max_bdd_nodes")
        n=self.nextid
        self.nextid+=1
        self.nodes[n]=key
        self.unique[key]=n
        return n

    def from_assignments(self,items):
        values=tuple(sorted(set(items)))
        def rec(vals,depth):
            if not vals:return 0
            if depth==24:return 1
            bit=self.order[depth]
            lo=[v for v in vals if not (v>>bit)&1]
            hi=[v for v in vals if (v>>bit)&1]
            return self.node(depth,rec(lo,depth+1),rec(hi,depth+1))
        return rec(values,0)

    def land(self,a,b):
        if not a or not b:return 0
        if a==1:return b
        if b==1:return a
        if a==b:return a
        if a>b:a,b=b,a
        key=(a,b)
        if key in self.apply_cache:return self.apply_cache[key]
        la,lo_a,hi_a=self.nodes[a]
        lb,lo_b,hi_b=self.nodes[b]
        depth=min(la,lb)
        a0,a1=(lo_a,hi_a) if la==depth else (a,a)
        b0,b1=(lo_b,hi_b) if lb==depth else (b,b)
        out=self.node(depth,self.land(a0,b0),self.land(a1,b1))
        self.apply_cache[key]=out
        self.max_apply_cache=max(self.max_apply_cache,len(self.apply_cache))
        return out

    def count(self,root):
        @functools.lru_cache(None)
        def count_from(n,depth):
            if n==0:return 0
            if n==1:return 1<<(24-depth)
            level,lo,hi=self.nodes[n]
            assert level>=depth
            return (1<<(level-depth))*(count_from(lo,level+1)
                                       +count_from(hi,level+1))
        return count_from(root,0)

def pack(iu,d,g):
    return iu|(d<<8)|(g<<16)

def factors():
    left={}
    right=defaultdict(list)
    for a in range(1,16):
        alpha=(0,a)
        rows=[]
        for iu in range(N):
            u=decode(iu)
            x=inv(u,KEYS[:2])
            delta=xor(fw(xor(x,alpha),KEYS[:2]),u)
            d=encode(delta)
            gamma=encode(differential(u,delta,KEYS[2:3]))
            rows.append(pack(iu,d,gamma))
        left[a]=rows

    for iu in range(N):
        u=decode(iu)
        for d in range(N):
            delta=decode(d)
            beta=differential(u,delta,KEYS[2:])
            if beta[1]!=0 or beta[0]==0:continue
            gamma=encode(differential(u,delta,KEYS[2:3]))
            right[beta[0]].append(pack(iu,d,gamma))
    return left,right

def run(order,max_nodes):
    t0=time.monotonic()
    left,right=factors()
    manager=BDD(order,max_nodes)
    try:
        lbd={a:manager.from_assignments(v) for a,v in left.items()}
        rbd={b:manager.from_assignments(v) for b,v in right.items()}
        baseline=ddt(KEYS)
        positive=0
        maximum=0
        for a in range(1,16):
            for b in range(1,16):
                lhs=lbd[a]
                rhs=rbd.get(b,0)
                joined=manager.land(lhs,rhs)
                value=manager.count(joined)
                maximum=max(maximum,value)
                expected=baseline[encode((0,a))][encode((b,0))]
                assert value==expected,(a,b,value,expected)
                positive+=int(value>0)
        return dict(status="complete",compared_endpoints=225,
                    positive_endpoints=positive,
                    peak_DDT_coefficient=maximum,
                    bdd_nodes=manager.nextid-2,
                    bdd_apply_cache=manager.max_apply_cache,
                    complete_base_delta_gamma_bits_kept=24,
                    elapsed_s=round(time.monotonic()-t0,3))
    except Limit as exc:
        return dict(status="LIMIT",reason=str(exc),
                    bdd_nodes=manager.nextid-2,
                    elapsed_s=round(time.monotonic()-t0,3))

def main():
    cli=argparse.ArgumentParser()
    cli.add_argument("--max-nodes",type=int,default=200000)
    args=cli.parse_args()
    contiguous=list(range(24))
    interleaved=[v for bit in range(8) for v in (bit,8+bit,16+bit)]
    for label,order in [("contiguous",contiguous),("interleaved",interleaved)]:
        result=run(order,args.max_nodes)
        print("LIFTED_J_BDD",label,json.dumps(result,sort_keys=True),flush=True)
        assert result["status"]=="complete",result
    print("LIFTED_J_BDD_GATE_OK",flush=True)

if __name__=="__main__":
    main()
