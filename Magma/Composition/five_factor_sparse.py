#!/usr/bin/env python3
"""Experimental exact integer-weight sparse elimination of five real Magma g chains.

Unlike opposite_five_tagged.py, the COUNTING engine here uses no SMT:
local RFC dual-carry digit tables and rotated bit-tag equality factors
are joined over finite domains, multiplying and summing integer weights.
This is a bounded prototype. If a join requires too many rows or too
much time, status=LIMIT with no exact DDT claim.

The first-difference 0x80000000 with k0=0 uses the proved top-nibble
g0 simplification; other differences and outer keys use all five full
chains. One- and two-nibble toy variants are also supported solely for
independent exact semiring regression (they are NOT RFC Magma).
"""
import argparse
import json
import math
import sys
import time
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
from verify_nround import BOX

K=(0,0x2056,0xfdfa7789,0xf0f8d960,0)
MASK=0xffffffff

class Limit(Exception):
    pass

class Factor:
    __slots__=("scope","rows")
    def __init__(self,scope,rows):
        self.scope=tuple(scope)
        self.rows=dict(rows)

def make(scope, assignment_rows):
    scope=tuple(scope)
    out=defaultdict(int)
    for values in assignment_rows:
        out[tuple(values)]+=1
    return Factor(scope,out)

def pair_step(i,k,d,x,c):
    y=x+k+(c&1)
    yp=(x^d)+k+((c>>1)&1)
    u=BOX[i][y&15]
    v=BOX[i][yp&15]
    return u,u^v,(y>>4)|((yp>>4)<<1)

def build(keys,a,b,nibbles=8,rotation=None):
    assert nibbles in (1,2,8)
    mask=(1 << (4*nibbles))-1
    assert len(keys)==5 and all(0<=v<=mask for v in keys)
    assert 0<=a<=mask and 0<=b<=mask
    if rotation is None: rotation={1:1,2:3,8:11}[nibbles]
    assert 0<=rotation<4*nibbles
    simple=(nibbles==8 and a==0x80000000 and keys[0]==0)
    bits={}
    factors=[]
    def label(name,size):
        if name is None:return None
        assert name not in bits or bits[name]==size
        bits[name]=size
        return name
    def x(j,i): return label(f"x{j}:{i}",4) if not simple or j!=0 or i==7 else None
    def d(j,i): return label(f"D{j}:{i}",4) if not simple or j!=1 or i in (1,2) else None
    def carry(j,i): return label(f"C{j}:{i}",2) if 1<=i<nibbles and (not simple or j!=0) else None
    def tag(typ,j,position):
        if typ=="U" and j in (0,4):return None
        if simple and typ=="E" and j==0 and position//4!=7:return None
        return label(f"{typ}{j}:{position}",1)

    for j in range(5):
        for i in range(nibbles):
            if simple and j==0 and i!=7: continue
            xn=x(j,i)
            din=d(j,i) if j in (1,2,3) else None
            ci=carry(j,i)
            co=carry(j,i+1)
            e=[tag("E",j,4*i+pos) for pos in range(4)]
            u=[tag("U",j,4*i+pos) for pos in range(4)] if 1<=j<=3 else []
            scope=[v for v in [xn,din,ci,co,*e,*u] if v is not None]
            rows=[]
            for xnib in range(16):
                for dnib in range(16) if din is not None else [
                        ((a if j==0 else b) >> (4*i))&15 if j in (0,4) else 0]:
                    for inc in (range(4) if ci else (0,)):
                        unib,enib,outc=pair_step(i,(keys[j]>>(4*i))&15,
                                                 dnib,xnib,inc)
                        values={xn:xnib}
                        if din: values[din]=dnib
                        if ci: values[ci]=inc
                        if co: values[co]=outc
                        for pos,v in enumerate(e):values[v]=(enib>>pos)&1
                        for pos,v in enumerate(u):values[v]=(unib>>pos)&1
                        rows.append(tuple(values[v] for v in scope))
            factors.append(make(scope,rows))

    def add_constraint(scope, tuples):
        factors.append(make(scope,tuples))

    def one_bit(dn,bit,value):
        if dn is None:
            assert value==0
            return
        add_constraint([dn],((v,) for v in range(16) if ((v>>bit)&1)==value))

    def single(dn,bit,tg,offset=0):
        if tg is None:
            one_bit(dn,bit,offset)
            return
        assert dn is not None
        add_constraint([dn,tg],
                       ((v,((v>>bit)&1)^offset) for v in range(16)))

    def xor3(tn,pn,bit,tg):
        assert tn is not None and tg is not None
        if pn is None:
            single(tn,bit,tg)
        else:
            add_constraint([tn,pn,tg],((t,p,((t^p)>>bit)&1)
                       for t in range(16) for p in range(16)))

    def base3(lv,rv,bit,output_bit):
        if lv is None:return
        assert rv is not None and output_bit is not None
        add_constraint([lv,rv,output_bit],
                    ((left,right,((left^right)>>bit)&1)
                     for left in range(16) for right in range(16)))

    for pos in range(4*nibbles):
        i=pos//4
        bit=pos%4
        source=(pos-rotation)%(4*nibbles)
        pn=d(1,i)
        qn=d(2,i)
        tn=d(3,i)
        single(pn,bit,tag("E",0,source))
        single(qn,bit,tag("E",1,source),(a>>pos)&1)
        xor3(tn,pn,bit,tag("E",2,source))
        single(qn,bit,tag("E",3,source),(b>>pos)&1)
        single(tn,bit,tag("E",4,source))
        # x0 corresponds to the real first g base x1; x1=r, x2=z,
        # x3=x4, x4=x5. Base equations match opposite_five_fiber.py.
        base3(x(0,i),x(2,i),bit,tag("U",1,source))
        base3(x(3,i),x(1,i),bit,tag("U",2,source))
        base3(x(4,i),x(2,i),bit,tag("U",3,source))
    return bits,factors

def join(a,b,max_rows,deadline,stats):
    common=[v for v in a.scope if v in b.scope]
    ia=[a.scope.index(v) for v in common]
    ib=[b.scope.index(v) for v in common]
    nbs=[v for v in b.scope if v not in a.scope]
    src=[b.scope.index(v) for v in nbs]
    union=a.scope+tuple(nbs)
    # Construct the smaller index. No probabilistic approximation.
    if len(a.rows)>len(b.rows):
        return join(b,a,max_rows,deadline,stats)
    index=defaultdict(list)
    for key,weight in a.rows.items():
        index[tuple(key[i] for i in ia)].append((key,weight))
    output=defaultdict(int)
    for k,(key_b,weight_b) in enumerate(b.rows.items()):
        if (k&4095)==0 and time.monotonic()>deadline:raise Limit("max_seconds")
        for key_a,weight_a in index.get(tuple(key_b[i] for i in ib),()):
            output[key_a+tuple(key_b[i] for i in src)]+=weight_a*weight_b
            stats["join_pairs"]+=1
            if len(output)>max_rows:raise Limit("max_rows_in_join")
    stats["peak_factor_rows"]=max(stats["peak_factor_rows"],len(output))
    return Factor(union,output)

def project(f,v):
    i=f.scope.index(v)
    scope=f.scope[:i]+f.scope[i+1:]
    rows=defaultdict(int)
    for k,mass in f.rows.items():
        rows[k[:i]+k[i+1:]]+=mass
    return Factor(scope,rows)

def count_sparse(widths,factors,max_rows=100000,max_seconds=30,progress=True,
                 strategy="singleton"):
    deadline=time.monotonic()+max_seconds
    stats=dict(eliminations=0,join_pairs=0,peak_factor_rows=max(
        map(lambda f:len(f.rows),factors),default=0),peak_scope_bits=0,
        start_factor_count=len(factors),start_variables=len(widths))
    start=time.monotonic()
    try:
        while any(f.scope for f in factors):
            if time.monotonic()>deadline:raise Limit("max_seconds")
            appearances=defaultdict(list)
            for i,f in enumerate(factors):
                for v in f.scope:appearances[v].append(i)
            # Choose the smallest actual factor bucket, with cheap
            # one-factor eliminations first.
            def cost(v):
                bucket=[factors[i] for i in appearances[v]]
                scope=set().union(*(set(f.scope) for f in bucket))
                scope_bits=sum(widths[x] for x in scope)
                logs=sum(math.log2(1+len(f.rows)) for f in bucket)
                if strategy=="singleton":
                    return (len(bucket)!=1,scope_bits,logs,len(bucket),v)
                if strategy=="scope":
                    return (scope_bits,logs,len(bucket),v)
                if strategy=="sparse":
                    # Uniform-support estimate of a bucket join,
                    # discounted by each repeated shared variable.
                    repeats=sum(widths[w]*(sum(w in f.scope for f in bucket)-1)
                                for w in scope)
                    prediction=max(0,logs-repeats-widths[v])
                    return (round(prediction,3),scope_bits,len(bucket),v)
                raise ValueError(strategy)
            v=min(appearances,key=cost)
            locations=set(appearances[v])
            bucket=[factors[i] for i in sorted(locations)]
            factors=[f for i,f in enumerate(factors) if i not in locations]
            scope=set().union(*(set(f.scope) for f in bucket))
            stats["peak_scope_bits"]=max(stats["peak_scope_bits"],
                                         sum(widths[w] for w in scope))
            while len(bucket)>1:
                # Choose the closest/smallest pair to restrict intermediates.
                best=None
                for i in range(len(bucket)):
                    for j in range(i+1,len(bucket)):
                        a,b=bucket[i],bucket[j]
                        shared=set(a.scope)&set(b.scope)
                        est=(math.log2(1+len(a.rows))+math.log2(1+len(b.rows))
                             -sum(widths[x] for x in shared))
                        key=(est,len(set(a.scope)|set(b.scope)),i,j)
                        if best is None or key<best:best=key
                i,j=best[-2:]
                combined=join(bucket[i],bucket[j],max_rows,deadline,stats)
                bucket=[f for k,f in enumerate(bucket) if k not in (i,j)]
                bucket.append(combined)
            reduced=project(bucket[0],v)
            if not reduced.rows:
                stats["elapsed_seconds"]=round(time.monotonic()-start,3)
                return dict(status="complete",weighted_count=0,**stats)
            factors.append(reduced)
            stats["peak_factor_rows"]=max(stats["peak_factor_rows"],len(reduced.rows))
            stats["eliminations"]+=1
            if progress and stats["eliminations"]%15==0:
                print("SPARSE_PROGRESS",json.dumps(dict(step=stats["eliminations"],
                     eliminated=v,peak_rows=stats["peak_factor_rows"],
                     latest_rows=len(reduced.rows),
                     peak_scope_bits=stats["peak_scope_bits"])),flush=True)
        total=1
        for f in factors:
            assert not f.scope
            total*=f.rows.get((),0)
        stats["elapsed_seconds"]=round(time.monotonic()-start,3)
        return dict(status="complete",weighted_count=total,**stats)
    except Limit as e:
        stats["elapsed_seconds"]=round(time.monotonic()-start,3)
        return dict(status="LIMIT",reason=str(e),**stats)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--keys",default=",".join(hex(k) for k in K))
    p.add_argument("--alpha",type=lambda s:int(s,0),default=0x80000000)
    p.add_argument("--beta",type=lambda s:int(s,0),default=0x681e60a7)
    p.add_argument("--nibbles",type=int,choices=(1,2,8),default=8)
    p.add_argument("--rotate",type=int)
    p.add_argument("--max-rows",type=int,default=100000)
    p.add_argument("--max-seconds",type=int,default=30)
    p.add_argument("--strategy",choices=("singleton","scope","sparse"),default="singleton")
    p.add_argument("--quiet",action="store_true")
    args=p.parse_args()
    keys=tuple(int(v,0) for v in args.keys.split(","))
    widths,factors=build(keys,args.alpha,args.beta,args.nibbles,args.rotate)
    print("FIVE_SPARSE_START",json.dumps(dict(variables=len(widths),
           factors=len(factors),initial_rows=sum(len(f.rows) for f in factors))),flush=True)
    result=count_sparse(widths,factors,args.max_rows,args.max_seconds,
                        not args.quiet,args.strategy)
    print("FIVE_SPARSE_RESULT",json.dumps(result,sort_keys=True),flush=True)

if __name__=="__main__":
    main()
