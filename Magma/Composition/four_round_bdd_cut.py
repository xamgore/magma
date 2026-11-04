#!/usr/bin/env python3
"""Exact bounded 5-round counting by a 4-round BDD *partial output* filter.

For a real five-round Feistel input (0,a) and output (b,0),
the fourth-round right-half difference MUST equal b. A symbolic BDD
computes that predicate using the actual four-round carries/S-boxes.
Every satisfying concrete base state is then replayed through all
five rounds and accepted only if its *full* output difference is (b,0).

This is an exact projection followed by candidate filtering, not an
independent DDT product. A canonical XOR-pair representative halves
the candidate count and doubles the final integer mass.
Resource caps return LIMIT, never an inferred exact zero.

The implementation targets 4-/8-/12-bit Feistel toys using 1..3
authentic RFC 4-bit S-boxes. This is not full Magma 32-bit.
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
from boundary_g_chain_bdd import eq_word
from five_factor_sparse_regression import feistel_toy

class CandidateLimit(Exception):pass

def enumerate_bdd(M,root,max_candidates):
    """Yield complete original-variable bit sets, not internal BDD labels."""
    count=0
    def visit(n,depth,bits):
        nonlocal count
        if n==0:return
        if n==1:
            if count+(1 << (M.num_vars-depth))>max_candidates:
                raise CandidateLimit("candidate_cap")
            for rem in range(1 << (M.num_vars-depth)):
                tmp=bits
                for i in range(M.num_vars-depth):
                    if (rem>>i)&1:tmp|=1<<M.order[depth+i]
                count+=1
                yield tmp
            return
        level,lo,hi=M.nodes[n]
        assert level>=depth
        for skip in range(1 << (level-depth)):
            tmp=bits
            for pos in range(level-depth):
                if skip>>pos&1:tmp|=1<<M.order[depth+pos]
            yield from visit(lo,level+1,tmp)
            yield from visit(hi,level+1,tmp|(1<<M.order[level]))
    yield from visit(root,0,0)

def count(w,rot,keys,a,b,max_nodes=250000,max_candidates=100000,
          seconds=10,fixed=None,canonical=True):
    assert w in (4,8,12) and 0<a<(1<<w)
    start=time.monotonic()
    order=[j*w+i for i in range(w) for j in (0,1)]
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
        dl=[0]*w
        dr=[(a>>i)&1 for i in range(w)]
        for key in keys[:4]:
            base_g=g(M,r,key,rot)
            shifted_g=g(M,sxor(M,r,dr),key,rot)
            next_diff=sxor(M,dl,sxor(M,base_g,shifted_g))
            l,r=r,sxor(M,l,base_g)
            dl,dr=dr,next_diff
        care=eq_word(M,dr,b)
        necessary_mass=M.count(care)
        if necessary_mass>max_candidates:raise CandidateLimit("candidate_cap")
        passed=0
        for bits in enumerate_bdd(M,care,max_candidates):
            for i,v in fixed.items():
                if v:bits|=1<<i
            L=(bits>>0)&((1<<w)-1)
            R=(bits>>w)&((1<<w)-1)
            y=feistel_toy(keys,L,R,w//4,rot)
            yp=feistel_toy(keys,L,R^a,w//4,rot)
            if (y[0]^yp[0],y[1]^yp[1])==(b,0):
                passed+=1
        return dict(status="complete",weighted_count=passed*(2 if canonical else 1),
                    fourth_round_candidates=necessary_mass,
                    peak_nodes=len(M.unique),
                    elapsed_s=round(time.monotonic()-start,3))
    except (Limit,CandidateLimit) as e:
        return dict(status="LIMIT",reason=str(e),peak_nodes=len(M.unique),
                    elapsed_s=round(time.monotonic()-start,3))

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--max-nodes",type=int,default=300000)
    p.add_argument("--max-candidates",type=int,default=100000)
    p.add_argument("--seconds",type=int,default=10)
    args=p.parse_args()
    cir.sbox_4=anf_sbox
    for w,rot,a,b,expected in [(4,1,8,4,4),(8,3,1,215,2),(12,7,1,121,548)]:
        for fixed in ({}, {i:0 for i in range(4)}):
            if w==4 and fixed:continue
            res=count(w,rot,(1,2,3,4,5),a,b,args.max_nodes,
                      args.max_candidates,args.seconds,fixed)
            if res["status"]=="complete":
                if not fixed: assert res["weighted_count"]==expected,res
                else: assert 0<=res["weighted_count"]<=expected,res
            print("FOUR_ROUND_BDD_CUT",json.dumps(dict(word_bits=w,
                alpha=a,beta=b,fixed_bits=len(fixed),expected=expected,**res),
                sort_keys=True),flush=True)
if __name__=="__main__":main()
