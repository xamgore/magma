#!/usr/bin/env python3
"""Regression of a genuine weighted finite-domain five-g factor join.

For a 4-bit/one-S-box Feistel toy, compare complete integer-weight
variable elimination with an independently coded exhaustive five-round
DDT. Also enforce that a resource-limited *real* 32-bit run must never
be mislabeled as a completed count. The toy is NOT RFC Magma.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import random
import time
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse import BOX,build,count_sparse

def g_toy(k,x,nibbles,rot):
    bits=4*nibbles
    mask=(1<<bits)-1
    word=(x+k)&mask
    sb=sum(BOX[i][(word>>(4*i))&15]<<(4*i) for i in range(nibbles))
    return ((sb<<rot)|(sb>>(bits-rot)))&mask

def feistel_toy(keys,left,right,nibbles=1,rot=1):
    for key in keys:
        left,right=right,left^g_toy(key,right,nibbles,rot)
    return left,right

def brute(keys,a,b,nibbles=1,rot=1):
    mask=(1<<(4*nibbles))-1
    count=0
    for left in range(mask+1):
        for right in range(mask+1):
            x=feistel_toy(keys,left,right,nibbles,rot)
            y=feistel_toy(keys,left,right^a,nibbles,rot)
            if x[0]^y[0]==b and x[1]^y[1]==0:
                count+=1
    return count

def main():
    rng=random.Random(48135)
    cases=[
        ((1,2,3,4,5),8,4),
        ((1,2,3,4,5),0,0),
        ((1,2,3,4,5),1,1),
        ((1,2,3,4,5),8,7),
        ((15,0,12,10,7),3,5),
        ((0,0,0,0,0),1,3),
    ]
    for _ in range(4):
        keys=tuple(rng.randrange(16) for _ in range(5))
        a,b=rng.randrange(16),rng.randrange(16)
        cases.append((keys,a,b))
    started=time.monotonic()
    rows=[]
    for idx,(keys,a,b) in enumerate(cases):
        reference=brute(keys,a,b)
        widths,factors=build(keys,a,b,1,1)
        result=count_sparse(widths,factors,300000,12,False)
        assert result["status"]=="complete",result
        assert result["weighted_count"]==reference,(idx,keys,a,b,reference,result)
        rows.append(dict(test=idx,alpha=a,beta=b,count=reference,
                         max_rows=result["peak_factor_rows"]))
        print("TOY_FIVE_WEIGHTED_EXACT",idx,reference,flush=True)
    keys=(0,0x2056,0xfdfa7789,0xf0f8d960,0)
    widths,factors=build(keys,0x80000000,0x681e60a7)
    limit=count_sparse(widths,factors,30000,8,False)
    assert limit["status"]=="LIMIT" or (
        limit["status"]=="complete" and limit["weighted_count"]==2),limit
    if limit["status"]=="LIMIT":
        assert "weighted_count" not in limit
    print("REAL_32_BOUND_IS_HONEST",json.dumps(limit,sort_keys=True),flush=True)
    print("FIVE_SPARSE_REGRESSION_OK",
          json.dumps(dict(cases=rows,seconds=round(time.monotonic()-started,3))),flush=True)

if __name__=="__main__":
    main()
