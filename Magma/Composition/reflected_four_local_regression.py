#!/usr/bin/env python3
"""Reproducible exact 225-cell regression of reflected local carry-join.

All 225 nonzero 4-bit-word opposite boundary DDT entries are
counted via the LOCAL S-box/carry/rotation/real-base factor network,
compared against an independent exhaustive nine-round Feistel.
Also asserts a 2-nibble LIMIT can never be reported as a zero
and compares structural full-width scopes without dense allocation.
"""
import json,time
from reflected_four_local_join import build,direct,profile
from reflected_four_conditioning import restrict
from five_factor_sparse import count_sparse

def main():
    t=time.monotonic()
    k=(5,6,7,8)
    zeros=positive=0
    peak=0
    total_witnesses=0
    for a in range(1,16):
        for b in range(1,16):
            widths,factors,scopes=build(k,a,b,1,1)
            got=count_sparse(widths,factors,90000,5,False,strategy='sparse')
            assert got['status']=='complete',(a,b,got)
            expected=direct(k,a,b,1,1)
            assert got['weighted_count']==expected,(a,b,got,expected)
            peak=max(peak,got['peak_factor_rows'])
            zeros+=(expected==0)
            positive+=(expected>0)
            total_witnesses+=expected
    assert (zeros,positive,total_witnesses)==(149,76,188)
    print('REFLECTED_LOCAL_ALL_225_COMPLETE',
          json.dumps(dict(cases=225,zeros=zeros,positives=positive,
            summed_ddt=total_witnesses,peak_rows=peak,
            seconds=round(time.monotonic()-t,3)),sort_keys=True),flush=True)
    k2=(1,2,3,4)
    widths,factors,scopes=build(k2,1,0xd7,2,3)
    assert direct(k2,1,0xd7,2,3)==0
    results=[]
    for strategy in ('sparse','scope'):
        got=count_sparse(widths,factors,250000,6,False,strategy=strategy)
        assert (got['status']=='complete' and got['weighted_count']==0) or \
            (got['status']=='LIMIT' and 'weighted_count' not in got)
        results.append(dict(strategy=strategy,status=got['status'],
                       eliminated=got['eliminations'],
                       max_rows=got['peak_factor_rows']))
    w2,f2=restrict(widths,factors,{'Xu0:0':0})
    conditional=count_sparse(w2,f2,250000,6,False,strategy='sparse')
    assert (conditional['status']=='LIMIT' and
            'weighted_count' not in conditional) or (
            conditional['status']=='complete' and
            conditional['weighted_count']==0)
    print('REFLECTED_LOCAL_8BIT_RESOURCE_GATE',
          json.dumps(dict(tested_exact_brute_zero=True,
            sparse_runs=results,one_tag_conditioned_status=conditional['status'],
            one_tag_conditional_eliminations=conditional['eliminations']),
          sort_keys=True),flush=True)
    w,_,scopes=build((0,0x2056,0xfdfa7789,0xf0f8d960),
                      0x80000000,0x80000000,8,11,True)
    peaks=profile(w,scopes)
    assert len(w)==312 and len(scopes)==192
    print('REFLECTED_LOCAL_32BIT_STRUCTURAL_GATE',
          json.dumps(dict(variables=len(w),factors=len(scopes),
            min_neighbor_scope_bits=peaks[0]['peak_scope_bits'],
            min_fill_scope_bits=peaks[1]['peak_scope_bits'],
            caveat='heuristic dense scopes; not actual lower bounds'),
            sort_keys=True),flush=True)
    print('REFLECTED_LOCAL_JOIN_REGRESSION_OK',flush=True)

if __name__=='__main__':main()
