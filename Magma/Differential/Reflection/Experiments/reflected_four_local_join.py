#!/usr/bin/env python3
"""Exact carry-preserving four-G crossing as a sparse Nat-semiring factor join.

Important: NO 4-round DDT marginals are multiplied. Two paired
trajectories (X,X') and (Y,Y') share the real four-round keys
k0..k3. Their base and XOR differences are linked at H outputs:
    H(Y)=J H(X), H(Y xor (0,b))=J H(X xor (a,0)).
Here words are 4*nibbles wide; real RFC S-boxes 0..nibbles-1,
modular carries and ROL 1/3/11 as configured.

The CSP variables include real base words X0..X5,Y0..Y5, their
derivative words, 2-bit paired addition carries, and the REAL
4-bit substituted output and derivative tags at every S-box.
All carry-in values at nibble 0 are zero; modulo-addition
final carries are intentionally discarded. The two crossings
are imposed by VARIABLE IDENTIFICATION, not by a permissive join.

Eliminating all CSP variables with exact integer sum-product
is the exact fixed-key nine-round boundary DDT. Each satisfying
assignment bijects to one genuine x base state: y is uniquely
determined by the first crossing. No auxiliary assignment
multiplicity and NO 2^64 plaintext enumeration.

This is a BOUNDED SPARSE BASELINE. It is NOT automatically
a scalable 32-bit solver: row/frontier growth yields LIMIT,
which may never be reported as a count. An 8-nibble network
can be analyzed structurally without allocating huge factors.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse import Factor,make,count_sparse,pair_step
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy

def build(keys,a,b,nibbles=1,rotation=None,structure_only=False):
    assert 1<=nibbles<=8 and len(keys)==4
    width=4*nibbles
    mask=(1<<width)-1
    rot=(1 if nibbles==1 else 3 if nibbles==2 else 11) if rotation is None else rotation
    assert all(0<=k<=mask for k in keys) and 0<=a<=mask and 0<=b<=mask
    assert 0<=rot<width
    widths={}
    factors=[]
    scopes=[]
    def var(name,n_bits=4):
        assert name not in widths or widths[name]==n_bits
        widths[name]=n_bits
        return name
    def X(chain,j,i):
        if chain=='Y' and j in (4,5):
            return X('X',9-j,i)  # y4=x5; y5=x4
        return var(f'{chain}x{j}:{i}')
    def D(chain,j,i):
        if chain=='Y' and j in (4,5):
            return D('X',9-j,i)  # dy4=dx5; dy5=dx4
        if chain=='X' and j in (0,1):
            return (None,((a if j==0 else 0)>>(4*i))&15)
        if chain=='Y' and j in (0,1):
            return (None,((0 if j==0 else b)>>(4*i))&15)
        return (var(f'{chain}d{j}:{i}'),None)
    def factor(scope,rows):
        scope=tuple(dict.fromkeys(scope))
        assert len(scope)==len(set(scope))
        scopes.append(scope)
        if not structure_only:
            factors.append(make(scope,rows))
    for chain in ('X','Y'):
      for j in range(4):
        for i in range(nibbles):
          xi=X(chain,j+1,i)
          din,dconst=D(chain,j+1,i)
          cin=var(f'{chain}c{j}:{i}',2) if i else None
          cout=var(f'{chain}c{j}:{i+1}',2) if i<nibbles-1 else None
          U=var(f'{chain}u{j}:{i}')
          E=var(f'{chain}e{j}:{i}')
          scope=[v for v in (xi,din,cin,cout,U,E) if v is not None]
          if structure_only:
              factor(scope,[])
              continue
          rows=[]
          for base in range(16):
            for diff in (range(16) if din else (dconst,)):
              for carry in (range(4) if cin else (0,)):
                u,e,next_c=pair_step(i,(keys[j]>>(4*i))&15,
                                     diff,base,carry)
                val={xi:base,U:u,E:e}
                if din:val[din]=diff
                if cin:val[cin]=carry
                if cout:val[cout]=next_c
                rows.append(tuple(val[v] for v in scope))
          factor(scope,rows)
    # Each nibble output x_{j+2}=x_j XOR ROL(U_j), idem
    # derivative d_{j+2}=d_j XOR ROL(E_j).
    # Rotation may splice TWO S-box nibbles; both are retained,
    # and are linked to the same local addition carries above.
    for chain in ('X','Y'):
      for j in range(4):
        for i in range(nibbles):
          sources=tuple(dict.fromkeys(((4*i+t-rot)%width)//4 for t in range(4)))
          assert len(sources)<=2
          for typ in ('base','diff'):
            if typ=='base':
                left=(X(chain,j,i),None)
                right=(X(chain,j+2,i),None)
                emit=lambda idx:var(f'{chain}u{j}:{idx}')
            else:
                left=D(chain,j,i)
                right=D(chain,j+2,i)
                emit=lambda idx:var(f'{chain}e{j}:{idx}')
            left_var,left_const=left
            right_var,right_const=right
            tags=[emit(q) for q in sources]
            scope=[v for v in (left_var,right_var,*tags) if v is not None]
            if structure_only:
                factor(scope,[])
                continue
            table=[]
            from itertools import product
            for ts in product(range(16),repeat=len(tags)):
              given=dict(zip(tags,ts))
              rotated=0
              for t in range(4):
                src=(4*i+t-rot)%width
                rotated|=((given[emit(src//4)]>>(src%4))&1)<<t
              for l in range(16) if left_var else (left_const,):
                r=l^rotated
                if right_var is None and r!=right_const:
                    continue
                val=dict(given)
                if left_var:val[left_var]=l
                if right_var:val[right_var]=r
                table.append(tuple(val[v] for v in scope))
            factor(scope,table)
    return widths,factors,scopes

def direct(keys,a,b,nibbles,rot):
    width=4*nibbles
    assert width<=8
    ks=list(keys)+list(reversed(keys))+[0]
    count=0
    for left in range(1<<width):
      for right in range(1<<width):
        x=feistel_toy(ks,left,right,nibbles,rot)
        y=feistel_toy(ks,left^a,right,nibbles,rot)
        count+=(x[0]^y[0],x[1]^y[1])==(0,b)
    return count

def profile(widths,scopes):
    from Magma.Differential.FiveRounds.Experiments.five_factor_width import eliminate
    return [eliminate(widths,scopes,strategy)
            for strategy in ('min-neighbor','min-fill')]

def run_case(keys,a,b,n,rot,max_rows,seconds,strategies):
    started=time.monotonic()
    widths,factors,scopes=build(keys,a,b,n,rot)
    profiles=profile(widths,scopes)
    print('REFLECTED_LOCAL_GRAPH',
          json.dumps(dict(nibbles=n,variables=len(widths),
            factors=len(factors),initial_rows=sum(len(f.rows) for f in factors),
            heuristic_profiles=profiles),sort_keys=True),flush=True)
    ref=direct(keys,a,b,n,rot)
    rows=[]
    for strategy in strategies:
        ws,ff,_=build(keys,a,b,n,rot)
        stats=count_sparse(ws,ff,max_rows,seconds,False,strategy=strategy)
        if stats['status']=='complete':
            assert stats['weighted_count']==ref,(keys,a,b,stats,ref)
        else:
            assert stats['status']=='LIMIT' and 'weighted_count' not in stats
        result=dict(strategy=strategy,status=stats['status'],
            ddt=stats.get('weighted_count'),independent_brute=ref,
            created_factors=len(ff),stats=stats,
            total_seconds=round(time.monotonic()-started,3))
        rows.append(result)
        print('REFLECTED_LOCAL_JOIN',json.dumps(result,sort_keys=True),flush=True)
    return rows

def main():
    cli=argparse.ArgumentParser()
    cli.add_argument('--max-rows',type=int,default=300000)
    cli.add_argument('--seconds',type=int,default=18)
    cli.add_argument('--structure32',action='store_true')
    cli.add_argument('--nibbles',type=int,default=1)
    cli.add_argument('--max-cases',type=int,default=3)
    args=cli.parse_args()
    if args.structure32:
        widths,_,scopes=build([0,0x2056,0xfdfa7789,0xf0f8d960],
                             0x80000000,0x80000000,8,11,True)
        print('FULL32_REFLECTED_LOCAL_SCOPE',
          json.dumps(dict(variables=len(widths),factors=len(scopes),
                          heuristic_profiles=profile(widths,scopes)),
                     sort_keys=True),flush=True)
        return
    if args.nibbles==1:
        cases=[((5,6,7,8),1,1),((5,6,7,8),8,4),
               ((1,2,3,4),8,7)]
        rot=1
    elif args.nibbles==2:
        cases=[((1,2,3,4),1,0xd7)]
        rot=3
    else:raise ValueError('only 1 or 2 nibble counted; full 32 structure only')
    for keys,a,b in cases[:args.max_cases]:
        run_case(keys,a,b,args.nibbles,rot,args.max_rows,
                 args.seconds,('scope','sparse','singleton'))

if __name__=='__main__':main()
