#!/usr/bin/env python3
"""Exact Shannon conditioning on selected *shared real* carry/tag/base variables.

Every complete run sums disjoint restrictions F[V=v] of the exact
reflected-four-G factor network, using integer weights. No DDT
marginal product, false projected join, or model-blocking heuristic.

This is a probe of compactly eliminating intermediate variables;
a single failing branch makes the TOTAL status LIMIT (without count).
"""
import argparse,json,sys,time
from collections import defaultdict
from reflected_four_local_join import build,direct
from five_factor_sparse import Factor,count_sparse

def restrict(widths,factors,assignments):
    assert all(v in widths and 0<=k<(1<<widths[v])
               for v,k in assignments.items())
    new_widths={v:n for v,n in widths.items() if v not in assignments}
    out=[]
    for f in factors:
        vals=[(i,assignments[v]) for i,v in enumerate(f.scope)
              if v in assignments]
        if not vals:
            out.append(f)
            continue
        keep=[i for i,v in enumerate(f.scope) if v not in assignments]
        scope=tuple(f.scope[i] for i in keep)
        rows=defaultdict(int)
        for row,weight in f.rows.items():
            if all(row[i]==n for i,n in vals):
                rows[tuple(row[i] for i in keep)]+=weight
        out.append(Factor(scope,rows))
    return new_widths,out

def run(keys,a,b,n,rot,variable,max_rows,seconds,strategy,branch_count):
    widths,factors,_=build(keys,a,b,n,rot)
    assert variable in widths,variable
    begun=time.monotonic()
    exact=direct(keys,a,b,n,rot)
    total=0
    rows=[]
    possible=1<<widths[variable]
    assert branch_count<=possible
    for i in range(branch_count):
        new_widths,new_factors=restrict(widths,factors,{variable:i})
        result=count_sparse(new_widths,new_factors,max_rows,seconds,
                            False,strategy=strategy)
        row=dict(value=i,status=result['status'],
                 ddt=result.get('weighted_count'),
                 seconds=result['elapsed_seconds'],
                 peak_rows=result['peak_factor_rows'],
                 eliminated=result['eliminations'],
                 reason=result.get('reason'))
        rows.append(row)
        print('REFLECTED_CONDITIONED_BRANCH',json.dumps(
            dict(variable=variable,**row),sort_keys=True),flush=True)
        if result['status']=='complete':
            total+=result['weighted_count']
        else:
            print('REFLECTED_CONDITIONED_TOTAL',json.dumps(dict(
                status='LIMIT',count=None,branches_completed=len(rows)-1,
                branches_total=possible,variable=variable,
                elapsed_s=round(time.monotonic()-begun,3)),
                sort_keys=True),flush=True)
            return rows
    if branch_count==possible:
        assert total==exact,(variable,total,exact)
        print('REFLECTED_CONDITIONED_TOTAL',json.dumps(dict(
            status='COMPLETE',count=total,brute=exact,
            branches_completed=possible,variable=variable,
            elapsed_s=round(time.monotonic()-begun,3)),
            sort_keys=True),flush=True)
    else:
        print('REFLECTED_CONDITIONED_TOTAL',json.dumps(dict(
            status='PARTIAL_PROBE',count=None,
            branches_completed=branch_count,branches_total=possible,
            variable=variable,elapsed_s=round(time.monotonic()-begun,3)),
            sort_keys=True),flush=True)
    return rows

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--variable',default='Xu0:0')
    p.add_argument('--nibbles',type=int,choices=(1,2),default=2)
    p.add_argument('--strategy',choices=('scope','sparse','singleton'),default='sparse')
    p.add_argument('--seconds',type=int,default=6)
    p.add_argument('--max-rows',type=int,default=300000)
    p.add_argument('--branch-count',type=int,default=16)
    a=p.parse_args()
    k=(1,2,3,4) if a.nibbles==2 else (5,6,7,8)
    av,bv,rot=(1,0xd7,3) if a.nibbles==2 else (1,1,1)
    run(k,av,bv,a.nibbles,rot,a.variable,a.max_rows,
        a.seconds,a.strategy,a.branch_count)

if __name__=='__main__':main()
