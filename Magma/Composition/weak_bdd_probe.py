#!/usr/bin/env python3
"""Weak-reference, garbage-collecting ROBDD prototype.

This is an exact pure-Python Boolean-function representation, NOT an
approximate counter. Unlike the earlier BDD, nodes not reachable from
currently live expression roots are reclaimed by Python reference
counting. The unique table and operation cache hold WEAK references,
so they do not permanently retain every intermediate circuit node.

Persistent live frontier and TOTAL CREATED node count are recorded
separately; stale cache keys cannot alias because every node has a
monotonically increasing identifier.

Only toy-length models are benchmarked. Some expressions may still
require huge live frontiers, and absent references cannot be inferred
as completed DDT zeros.
"""
import functools
import json
import sys
import time
import weakref
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from overlap_j_circuit_bdd import Limit
import overlap_j_circuit_bdd as circuit
import two_word_bdd_probe as two
from sbox_bdd_optimizer import anf_sbox

class Node:
    __slots__=("uid","depth","lo","hi","__weakref__")
    def __init__(self,uid,depth,lo,hi):
        self.uid,self.depth,self.lo,self.hi=uid,depth,lo,hi

class WeakROBDD:
    def __init__(self,num_vars,order,node_cap=250000,seconds=15):
        self.num_vars=num_vars
        self.order=order
        self.level_by_var={v:i for i,v in enumerate(order)}
        self.node_cap=node_cap
        self.deadline=time.monotonic()+seconds
        self.unique=weakref.WeakValueDictionary()
        self.appcache=weakref.WeakValueDictionary()
        self.notcache=weakref.WeakValueDictionary()
        self.uid_counter=2
        self.allocated=0
        self.peak_live=0
        self.ands=0

    @staticmethod
    def uid(v):
        return v if isinstance(v,int) else v.uid

    def mk(self,depth,lo,hi):
        if lo is hi or lo==hi:return lo
        key=(depth,self.uid(lo),self.uid(hi))
        entry=self.unique.get(key)
        if entry is not None:return entry
        if len(self.unique)>=self.node_cap:raise Limit("max_live_nodes")
        if self.uid_counter%8192==0 and time.monotonic()>self.deadline:
            raise Limit("max_seconds")
        obj=Node(self.uid_counter,depth,lo,hi)
        self.uid_counter+=1
        self.unique[key]=obj
        self.allocated+=1
        self.peak_live=max(self.peak_live,len(self.unique))
        return obj

    def var(self,idx):
        return self.mk(self.level_by_var[idx],0,1)

    def neg(self,n):
        if isinstance(n,int):return 1-n
        entry=self.notcache.get(n.uid)
        if entry is not None:return entry
        answer=self.mk(n.depth,self.neg(n.lo),self.neg(n.hi))
        if not isinstance(answer,int): self.notcache[n.uid]=answer
        return answer

    def op(self,which,a,b):
        if which=="and":
            if a==0 or b==0:return 0
            if a==1:return b
            if b==1:return a
            if a is b:return a
        elif which=="or":
            if a==1 or b==1:return 1
            if a==0:return b
            if b==0:return a
            if a is b:return a
        elif which=="xor":
            if a==0:return b
            if b==0:return a
            if a==1:return self.neg(b)
            if b==1:return self.neg(a)
            if a is b:return 0
        else:raise ValueError(which)

        if self.uid(a)>self.uid(b):a,b=b,a
        key=(which,self.uid(a),self.uid(b))
        prev=self.appcache.get(key)
        if prev is not None:return prev
        la,lo_a,hi_a=a.depth,a.lo,a.hi
        lb,lo_b,hi_b=b.depth,b.lo,b.hi
        depth=min(la,lb)
        a0,a1=(lo_a,hi_a) if la==depth else (a,a)
        b0,b1=(lo_b,hi_b) if lb==depth else (b,b)
        lo=self.op(which,a0,b0)
        hi=self.op(which,a1,b1)
        ans=self.mk(depth,lo,hi)
        if not isinstance(ans,int):
            self.appcache[key]=ans
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
            assert n.depth>=depth
            return (1<<(n.depth-depth))*(rec(n.lo,n.depth+1)
                                         +rec(n.hi,n.depth+1))
        return rec(root,0)

def main():
    circuit.sbox_4=anf_sbox
    two.BDD=WeakROBDD
    cases=[
        (4,1,8,4,150000),
        (8,3,1,215,200000),
        (12,7,1,121,200000),
    ]
    for w,rot,a,b,cap in cases:
        for base in ("input","middle"):
            output=two.solve(w,(1,2,3,4,5),a,b,rot,
                base,"interleave",cap,seconds=12)
            if output["status"]=="complete" and w<12:
                assert output["count"]=={4:4,8:2}[w]
            print("WEAK_BDD",json.dumps(dict(
                word_bits=w,base=base,**output),sort_keys=True),flush=True)

if __name__=="__main__":main()
