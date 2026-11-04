#!/usr/bin/env python3
"""Boundary-conditioned ROBDD for the TRUE five g derivatives.

Specialized to (0,a)->(b,0). Unlike two_full_trajectories,
the last round is NOT built with the complex perturbed base.
After four rounds, the output-left difference must be b.
Only under this exact condition, the fifth derivative is

  Delta g(k4, b, x5) = t

where t is the fourth previous difference. We may therefore
use fixed b as input of the fifth g derivative. The first
four rounds propagate exact *base and XOR-difference* words:

  newbase = (R, L XOR g(k,R))
  newdiff = (dR, dL XOR Delta g(k,R,dR))

Both output conditions are imposed on the same base/diff
trajectory, with no independent DDT multiplication.

A nonzero input difference also permits the exact quotient
by pair-swap: fix one toggled input bit to zero and double
the completed count. This prototype uses the first 1..n
real Magma S-boxes and fixed-key nibble arithmetic on
4-/8-/12-bit *toy* Feistel words. It is not RFC full 32bit.
"""
import argparse
import json
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
import overlap_j_circuit_bdd as cir
from overlap_j_circuit_bdd import BDD,Limit,sxor,g
from sbox_bdd_optimizer import anf_sbox
from two_word_bdd_probe import brute

def eq_word(M,word,desired):
    assert len(word)>0
    result=1
    for i,b in enumerate(word):
        bit=(desired>>i)&1
        result=M.land(result,b if bit else M.neg(b))
        if result==0:break
    return result

def eq_words(M,x,y):
    assert len(x)==len(y)
    result=1
    for a,b in zip(x,y):
        result=M.land(result,M.neg(M.xor(a,b)))
        if result==0:break
    return result

def exact(w,rot,keys,a,b,max_nodes=250000,
          seconds=10,order_name="interleave",fixed=None,
          canonical=True):
    start=time.monotonic()
    assert w in (4,8,12,16) and a
    if order_name=="interleave":
        order=[j*w+i for i in range(w) for j in (0,1)]
    elif order_name=="contiguous":
        order=list(range(2*w))
    elif order_name=="reverse-interleave":
        order=[j*w+i for i in range(w-1,-1,-1) for j in (0,1)]
    else:raise ValueError(order_name)
    fixed={} if fixed is None else dict(fixed)
    if canonical:
        bit=w+((a&-a).bit_length()-1)
        assert bit not in fixed
        fixed[bit]=0
    order=[i for i in order if i not in fixed]
    M=BDD(2*w-len(fixed),order,max_nodes,seconds)
    try:
        words=[[fixed[j*w+i] if j*w+i in fixed else M.var(j*w+i)
                for i in range(w)] for j in (0,1)]
        l,r=words
        d_l=[0]*w
        d_r=[(a>>i)&1 for i in range(w)]
        for key in keys[:4]:
            base_g=g(M,r,key,rot)
            shifted_r=sxor(M,r,d_r)
            shifted_g=g(M,shifted_r,key,rot)
            derivative=sxor(M,base_g,shifted_g)
            d_next=sxor(M,d_l,derivative)
            l,r=r,sxor(M,l,base_g)
            d_l,d_r=d_r,d_next

        # After 4 rounds (d4,d5)=(t,b). Both are genuine
        # functions of the same original two-word base.
        outer_condition=eq_word(M,d_r,b)
        if outer_condition==0:
            count=0
        else:
            # The last input difference *must* be the fixed b.
            last_g=g(M,r,keys[4],rot)
            last_shifted_g=g(M,sxor(M,r,[(b>>i)&1 for i in range(w)]),
                             keys[4],rot)
            last_derivative=sxor(M,last_g,last_shifted_g)
            inner_condition=eq_words(M,d_l,last_derivative)
            joined=M.land(outer_condition,inner_condition)
            count=M.count(joined)*(2 if canonical else 1)

        return dict(status="complete",count=count,
                    bdd_nodes=len(M.unique),cache=len(M.appcache),
                    elapsed_s=round(time.monotonic()-start,3))
    except Limit as err:
        return dict(status="LIMIT",reason=str(err),
                    bdd_nodes=len(M.unique),cache=len(M.appcache),
                    elapsed_s=round(time.monotonic()-start,3))

def main():
    args=argparse.ArgumentParser()
    args.add_argument("--max-nodes",type=int,default=250000)
    args.add_argument("--seconds",type=int,default=10)
    args.add_argument("--max-word-bits",type=int,default=12)
    a=args.parse_args()
    cir.sbox_4=anf_sbox
    for w,rot,d,b,expect in ((4,1,8,4,4),(8,3,1,215,2),(12,7,1,121,548)):
        if w>a.max_word_bits:continue
        for order in ("interleave","contiguous"):
            r=exact(w,rot,(1,2,3,4,5),d,b,a.max_nodes,a.seconds,order)
            if r["status"]=="complete":assert r["count"]==expect,(w,order,r)
            print("BOUNDARY_G_CHAIN_BDD",json.dumps(dict(word_bits=w,
                alpha=d,beta=b,rotation=rot,ordering=order,
                reference=expect,**r),sort_keys=True),flush=True)

if __name__=="__main__":main()
