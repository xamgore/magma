#!/usr/bin/env python3
"""Bounded *two-word*, not four-word, ROBDD for exact five-round toy DDT.

Key insight: in a deterministic Feistel permutation the middle XOR
difference delta is a FUNCTION of the real middle base u and fixed
input difference alpha. The earlier overlap_j_circuit_bdd.py allocated
independent Boolean variables for delta, doubling the dimension from
2*w to 4*w, then constrained them by a large join.

Here only the 2*w true base bits are decision variables. No models are
projected and a completed BDD count is the EXACT DDT multiplicity.
Compare input-base and middle-base parametrizations, and grouped
versus interleaved orders. RFC 4-bit S-boxes 0..n-1, modular carries,
and a configurable rotation are retained. 4/8/12/16 bit toy only,
NOT the full 32-bit Magma G.

A result with status LIMIT has no DDT value. Code uses deterministic
4-bit S-boxes from research/verify_nround.py, not Z3.
"""
import argparse
import json
import random
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from overlap_j_circuit_bdd import BDD,Limit,sxor,fr,inverse_fr,diff_constraints
from five_factor_sparse_regression import feistel_toy

def solve(w,keys,a,b,rot,base,order_name,max_nodes=250000,
          seconds=12,fixed=None,canonical_pair=False):
    began=time.monotonic()
    if order_name=="interleave":
        order=[i+j*w for i in range(w) for j in (0,1)]
    elif order_name=="contiguous":
        order=list(range(2*w))
    elif order_name=="reverse-interleave":
        order=[i+j*w for i in range(w-1,-1,-1) for j in (0,1)]
    elif order_name=="nibble":
        order=[j*w+i+t for i in range(0,w,4)
               for j in (0,1) for t in range(4)]
    else:raise ValueError(order_name)
    fixed={} if fixed is None else dict(fixed)
    if canonical_pair:
        assert base=="input" and a!=0, "canonical representative needs fixed input difference"
        pair_bit=w+((a&-a).bit_length()-1)
        assert pair_bit not in fixed, "pair representative bit must not be fixed by another condition"
        fixed[pair_bit]=0
    assert all(0<=k<2*w and v in (0,1) for k,v in fixed.items())
    order=[j for j in order if j not in fixed]
    manager=BDD(2*w-len(fixed),order,max_nodes,seconds)
    try:
        bits=[[fixed[j*w+i] if j*w+i in fixed else manager.var(j*w+i)
               for i in range(w)] for j in range(2)]
        center=(bits[0],bits[1])

        if base=="input":
            lhs=center
            rhs=(center[0],sxor(manager,center[1],
                                [int(bool((a>>i)&1)) for i in range(w)]))
            # Each g uses true carry coupling and all RFC S-boxes.
            for key in keys:
                lhs=fr(manager,lhs,key,rot)
                rhs=fr(manager,rhs,key,rot)
            want=(b,0)
        elif base=="middle":
            # u is actual state after first two rounds. The second
            # trajectory's full input is x^alpha, hence delta of u
            # is determined and must NOT be guessed independently.
            original=center
            for key in reversed(keys[:2]):
                original=inverse_fr(manager,original,key,rot)
            alternate=(original[0],sxor(manager,original[1],
                         [int(bool((a>>i)&1)) for i in range(w)]))
            for key in keys[:2]:
                alternate=fr(manager,alternate,key,rot)
            lhs=center
            rhs=alternate
            for key in keys[2:]:
                lhs=fr(manager,lhs,key,rot)
                rhs=fr(manager,rhs,key,rot)
            want=(b,0)
        else: raise ValueError(base)

        pred=diff_constraints(manager,lhs,rhs,want)
        count=manager.count(pred)*(2 if canonical_pair else 1)
        return dict(status="complete",count=count,
                    created_bdd_nodes=len(manager.unique),
                    cached_operations=len(manager.appcache),
                    elapsed_s=round(time.monotonic()-began,3))
    except Limit as e:
        return dict(status="LIMIT",reason=str(e),
                    created_bdd_nodes=len(manager.unique),
                    cached_operations=len(manager.appcache),
                    elapsed_s=round(time.monotonic()-began,3))

def brute(w,keys,a,b,rotation):
    assert w<=8
    total=0
    for l in range(1<<w):
        for r in range(1<<w):
            y=feistel_toy(keys,l,r,w//4,rotation)
            yp=feistel_toy(keys,l,r^a,w//4,rotation)
            total+=(y[0]^yp[0],y[1]^yp[1])==(b,0)
    return total

def sample_endpoint(w,keys,a,rotation,seed,attempts=100000):
    rng=random.Random(seed)
    for _ in range(attempts):
        l=rng.randrange(1<<w)
        r=rng.randrange(1<<w)
        y=feistel_toy(keys,l,r,w//4,rotation)
        yp=feistel_toy(keys,l,r^a,w//4,rotation)
        if y[1]==yp[1] and y[0]!=yp[0]:
            return y[0]^yp[0]
    return None

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--max-nodes",type=int,default=250000)
    cli.add_argument("--seconds",type=int,default=12)
    cli.add_argument("--max-word-bits",type=int,default=16)
    args=cli.parse_args()
    keys=(1,2,3,4,5)
    for w,rot,a in [(4,1,8),(8,3,1),(12,7,1),(16,11,1)]:
        if w>args.max_word_bits:continue
        b=({4:4,8:0xd7}.get(w)
           or sample_endpoint(w,keys,a,rot,seed=0x99af+w))
        if b is None:
            print("MIDDLE_BDD_NO_SAMPLE",w,flush=True)
            continue
        reference=brute(w,keys,a,b,rot) if w<=8 else None
        for base in ("input","middle"):
            for order in ("interleave","contiguous"):
                result=solve(w,keys,a,b,rot,base,order,args.max_nodes,args.seconds)
                if result["status"]=="complete":
                    if reference is not None:
                        assert result["count"]==reference,(w,base,order,result,reference)
                    else:
                        assert result["count"]>=2 and result["count"]%2==0,result
                print("TWO_WORD_BDD",json.dumps(dict(
                    word_bits=w,keys=list(keys),alpha=a,beta=b,
                    rotation=rot,parametrization=base,
                    ordering=order,bruteforce=reference,**result
                ),sort_keys=True),flush=True)

if __name__=="__main__":
    main()
