#!/usr/bin/env python3
"""Bounded circuit-built ROBDD of exact lifted 3+3 Feistel composition.

Unlike minterm enumeration, each g is assembled from boolean functions:
fixed-key modular addition (real carries), 4-bit S-box truth tables,
and rotate-left. The shared 2-word base u and its XOR difference delta
are represented by *symbolic* BDD variables.

The two overlapping three-round constraints are:
  left: F01^{-1}(u ^ delta) ^ F01^{-1}(u) = (0,a)
  right: F234(u ^ delta) ^ F234(u) = (b,0)
Thus model counting the conjunction is the exact 5-round DDT.
This experimental program targets 4-/8-bit-word Feistel toys using
RFC S-boxes 0..n-1; 32-bit RFC Magma is NOT solved by this prototype.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import functools
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX

class Limit(Exception):
    pass

class BDD:
    def __init__(self,num_vars,order,node_cap=200000,seconds=20):
        self.num_vars=num_vars
        self.order=order
        self.level_by_var={v:i for i,v in enumerate(order)}
        self.node_cap=node_cap
        self.deadline=time.monotonic()+seconds
        self.nodes={0:None,1:None}
        self.unique={}
        self.appcache={}
        self.notcache={0:1,1:0}
        self.hits=0
        self.ands=0

    def mk(self,depth,lo,hi):
        if lo==hi:return lo
        key=(depth,lo,hi)
        if key in self.unique:return self.unique[key]
        if len(self.unique)>=self.node_cap:raise Limit("max_nodes")
        if (len(self.unique)&4095)==0 and time.monotonic()>self.deadline:
            raise Limit("max_seconds")
        idx=len(self.nodes)
        self.nodes[idx]=key
        self.unique[key]=idx
        return idx

    def var(self,idx):
        return self.mk(self.level_by_var[idx],0,1)

    def neg(self,idx):
        if idx in self.notcache:return self.notcache[idx]
        d,lo,hi=self.nodes[idx]
        out=self.mk(d,self.neg(lo),self.neg(hi))
        self.notcache[idx]=out
        return out

    def op(self,which,a,b):
        if which=="and":
            if a==0 or b==0:return 0
            if a==1:return b
            if b==1:return a
            if a==b:return a
        elif which=="or":
            if a==1 or b==1:return 1
            if a==0:return b
            if b==0:return a
            if a==b:return a
        elif which=="xor":
            if a==0:return b
            if b==0:return a
            if a==1:return self.neg(b)
            if b==1:return self.neg(a)
            if a==b:return 0
        else: raise ValueError(which)
        if a>b:a,b=b,a
        key=(which,a,b)
        if key in self.appcache:
            self.hits+=1
            return self.appcache[key]
        na,la,ha=self.nodes[a]
        nb,lb,hb=self.nodes[b]
        level=min(na,nb)
        a0,a1=(la,ha) if na==level else (a,a)
        b0,b1=(lb,hb) if nb==level else (b,b)
        lo=self.op(which,a0,b0)
        hi=self.op(which,a1,b1)
        ans=self.mk(level,lo,hi)
        self.appcache[key]=ans
        if len(self.appcache)>4*self.node_cap:
            raise Limit("max_apply_cache")
        return ans

    def land(self,a,b):
        self.ands+=1
        return self.op("and",a,b)
    def lor(self,a,b):return self.op("or",a,b)
    def xor(self,a,b):return self.op("xor",a,b)

    def count(self,root):
        @functools.lru_cache(None)
        def rec(n,depth):
            if n==0:return 0
            if n==1:return 1<<(self.num_vars-depth)
            level,lo,hi=self.nodes[n]
            return (1<<(level-depth))*(rec(lo,level+1)+rec(hi,level+1))
        return rec(root,0)

def sxor(M,a,b):
    return [M.xor(x,y) for x,y in zip(a,b)]
def fixed_add(M,x,k):
    carry=0
    out=[]
    for i,bit in enumerate(x):
        if (k>>i)&1:
            out.append(M.neg(M.xor(bit,carry)))
            carry=M.lor(bit,carry)
        else:
            out.append(M.xor(bit,carry))
            carry=M.land(bit,carry)
    return out

def sbox_4(M,ins,table):
    assert len(ins)==4
    inv=[M.neg(bit) for bit in ins]
    cubes=[]
    for k in range(16):
        cube=1
        for i in range(4):
            cube=M.land(cube,ins[i] if (k>>i)&1 else inv[i])
        cubes.append(cube)
    out=[]
    for bit in range(4):
        a=0
        for k in range(16):
            if (table[k]>>bit)&1:
                a=M.lor(a,cubes[k])
        out.append(a)
    return out

def g(M,x,k,rotation):
    w=len(x)
    added=fixed_add(M,x,k)
    substituted=[]
    for j in range(w//4):
        substituted+=sbox_4(M,added[4*j:4*j+4],BOX[j])
    output=[None]*w
    for i,bit in enumerate(substituted):
        output[(i+rotation)%w]=bit
    return output

def fr(M,state,k,rotation):
    left,right=state
    return (right,sxor(M,left,g(M,right,k,rotation)))
def inverse_fr(M,state,k,rotation):
    left,right=state
    return (sxor(M,right,g(M,left,k,rotation)),left)

def diff_constraints(M,first,second,desired):
    p=1
    for bits_a,bits_b,word in zip(first,second,desired):
        for i,(x,y) in enumerate(zip(bits_a,bits_b)):
            d=M.xor(x,y)
            if (word>>i)&1:
                p=M.land(p,d)
            else:
                p=M.land(p,M.neg(d))
            if not p:return 0
    return p

def solve(w,k,a,b,rotation,order_name,max_nodes=200000,seconds=20,
          fixed_base_bits=0,fixed_base_value=0):
    start=time.monotonic()
    n=4*w
    if order_name=="bit-interleave":
        order=[g*w+i for i in range(w) for g in range(4)]
    else:
        order=list(range(n))
    assert 0<=fixed_base_bits<=w and 0<=fixed_base_value<(1<<fixed_base_bits)
    fixed={i:(fixed_base_value>>i)&1 for i in range(fixed_base_bits)}
    order=[i for i in order if i not in fixed]
    M=BDD(n-len(fixed),order,max_nodes,seconds)
    try:
        groups=[[fixed[gr*w+i] if gr*w+i in fixed else M.var(gr*w+i)
                 for i in range(w)] for gr in range(4)]
        u=(groups[0],groups[1])
        delta=(groups[2],groups[3])
        up=(sxor(M,u[0],delta[0]),sxor(M,u[1],delta[1]))

        # Two backward rounds; only u,delta are symbolic variables.
        before=u
        before_prime=up
        for key in reversed(k[:2]):
            before=inverse_fr(M,before,key,rotation)
            before_prime=inverse_fr(M,before_prime,key,rotation)
        left_condition=diff_constraints(M,before,before_prime,(0,a))

        # One shared round k2 plus the two succeeding rounds k3,k4.
        after=u
        after_prime=up
        for key in k[2:]:
            after=fr(M,after,key,rotation)
            after_prime=fr(M,after_prime,key,rotation)
        right_condition=diff_constraints(M,after,after_prime,(b,0))
        joined=M.land(left_condition,right_condition)
        count=M.count(joined)
        return dict(status="complete",ddt=count,bdd_nodes=len(M.unique),
                    apply_cache=len(M.appcache),and_calls=M.ands,
                    elapsed_s=round(time.monotonic()-start,3))
    except Limit as err:
        return dict(status="LIMIT",reason=str(err),
                    bdd_nodes=len(M.unique),
                    apply_cache=len(M.appcache),and_calls=M.ands,
                    elapsed_s=round(time.monotonic()-start,3))

def brute(w,k,a,b,rotation):
    from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy
    nibbles=w//4
    total=0
    for l in range(1<<w):
        for r in range(1<<w):
            x=feistel_toy(k,l,r,nibbles,rotation)
            y=feistel_toy(k,l,r^a,nibbles,rotation)
            total+=int((x[0]^y[0],x[1]^y[1])==(b,0))
    return total

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--max-nodes",type=int,default=150000)
    p.add_argument("--seconds",type=int,default=25)
    args=p.parse_args()
    k=(1,2,3,4,5)
    cases=[(4,1,8,4),(4,1,1,1),(8,3,1,0xd7),(8,3,0x80,0xb0),
           (8,3,1,1)]
    all_ok=True
    for w,rot,a,b in cases:
        expected=brute(w,k,a,b,rot)
        for order in ("bit-interleave","contiguous"):
            res=solve(w,k,a,b,rot,order,args.max_nodes,args.seconds)
            if w==4 and order=="bit-interleave":
                assert res["status"]=="complete",res
            if res["status"]=="complete": assert res["ddt"]==expected,(w,a,b,res,expected)
            else: all_ok=False
            print("CIRCUIT_J_JOIN",json.dumps(dict(word_bits=w,rot=rot,
                  alpha=a,beta=b,keys=list(k),ordering=order,
                  brute_ddt=expected,**res),sort_keys=True),flush=True)
    if all_ok:print("CIRCUIT_J_ALL_COMPLETE_OK",flush=True)
    else:print("CIRCUIT_J_LIMITS_RECORDED",flush=True)

if __name__=="__main__":
    main()
