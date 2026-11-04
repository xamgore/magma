#!/usr/bin/env python3
"""Toy diagnostic: how much shared base-state label is needed to join J3s?

Every support projection is a sound necessary filter for the five-round
transition: a real witness always survives. A positive in a coarsened
support join is NOT a real witness. This does not compute a DDT.
"""
import json
import time
from collections import defaultdict

from overlap_two_j_probe import (
    N, KEYS, decode, encode, fw, inv, rd, xor, differential, ddt,
)

def main():
    began=time.monotonic()
    full=ddt(KEYS)
    # For each possible output beta, collect the right lifted 3-block
    # candidates (delta2,gamma3,base u) that produce it.
    rights=defaultdict(list)
    for iu in range(N):
        u=decode(iu)
        for j in range(N):
            delta=decode(j)
            gamma=encode(differential(u,delta,KEYS[2:3]))
            beta=encode(differential(u,delta,KEYS[2:]))
            rights[beta].append((j,gamma,iu))
    labels=[0,1,2,3,4,5,6,7,8]
    projected_right={}
    for m in labels:
        mask=(1<<m)-1
        projected_right[m]={b:{(d,g,u&mask) for d,g,u in tuples}
                            for b,tuples in rights.items()}
    actual_positives=0
    false_positive={m:0 for m in labels}
    false_negative={m:0 for m in labels}
    survive={m:0 for m in labels}
    for a in range(1,16):
        alpha=(0,a)
        left=[]
        for iu in range(N):
            u=decode(iu)
            x=inv(u,KEYS[:2])
            delta=xor(fw(xor(x,alpha),KEYS[:2]),u)
            gamma=differential(u,delta,KEYS[2:3])
            left.append((encode(delta),encode(gamma),iu))
        proj_left={}
        for m in labels:
            mask=(1<<m)-1
            proj_left[m]={(d,g,u&mask) for d,g,u in left}
        for b in range(1,16):
            beta=encode((b,0))
            exact=full[encode(alpha)][beta]
            actual_positives+=int(exact>0)
            for m in labels:
                possible=bool(proj_left[m] & projected_right[m].get(beta,set()))
                survive[m]+=int(possible)
                false_positive[m]+=int(possible and exact==0)
                false_negative[m]+=int((not possible) and exact>0)
    assert all(v==0 for v in false_negative.values())
    assert false_positive[8]==0
    print("OVERLAP_SHARED_LABEL",json.dumps(dict(
        endpoint_pairs=225,true_positive_endpoints=actual_positives,
        true_zero_endpoints=225-actual_positives,
        base_u_bits_kept=labels,
        surviving_endpoint_pairs=survive,
        false_positive_zeros=false_positive,
        false_negatives=false_negative,
        elapsed_s=round(time.monotonic()-began,3)
    ),sort_keys=True),flush=True)
    print("OVERLAP_SHARED_LABEL_GATE_OK",flush=True)

if __name__=="__main__":
    main()
