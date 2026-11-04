#!/usr/bin/env python3
"""Materialized *one* reusable conditional four-round H kernel, toy scale.

For fixed four repeated keys H and every actual intermediate output base u,
cache t_H(u,alpha)=H(H^-1(u) XOR alpha) XOR u. Then for ANY
alpha,beta use the EXACT twisted self-correlation

    D_Q(alpha,beta) = SUM_u [t_H(Ju,beta)=J(t_H(u,alpha))].

This caches the same H kernel and reuses it for a grid of independent
differential queries. It avoids repeating the 9-round Feistel
evaluation for every endpoint cell, and it does not multiply
ordinary four-round DDT marginals. Independent direct replay follows.

This deliberately MATERIALIZES a state table: for 32-bit-word Magma
it would have 2**64 base labels, which is impossible. Its purpose
is to prove/benchmark *multi-query composition* as the next symbolic
carry-frontier/ADD target, not to suggest enumerating 2**64 states.
"""
import argparse,json,time
from five_factor_sparse_regression import feistel_toy,g_toy
from reflected_four_local_join import direct

def run(keys,nb,rot,inputs,outputs):
    w=4*nb
    mask=(1<<w)-1
    total=1<<(2*w)
    def enc(p):return ((p[0]&mask)<<w)|(p[1]&mask)
    def dec(u):return u>>w,u&mask
    def J(u):return ((u&mask)<<w)|(u>>w)
    def H(p):return feistel_toy(keys,*p,nb,rot)
    def invH(p):
        l,r=p
        for k in reversed(keys):
            l,r=(r^g_toy(k,l,nb,rot)),l
        return l,r
    # Cache the inverse H coordinate map only once, for all queries.
    start=time.monotonic()
    preimages=[]
    for u in range(total):
        x=invH(dec(u))
        assert enc(H(x))==u
        preimages.append(x)
    t_inverse=round(time.monotonic()-start,4)
    # Store the same conditional H operator at different input
    # difference labels; outputs are full-state difference words.
    def make_response(d):
        response=[]
        for u,x in enumerate(preimages):
            shifted=(x[0]^d[0],x[1]^d[1])
            response.append(enc(H(shifted))^u)
        return response
    alphas={(a,0) for a in inputs}
    betas={(0,b) for b in outputs}
    responses={}
    for d in sorted(alphas|betas):
        responses[d]=make_response(d)
    prepare=round(time.monotonic()-start,4)
    count={}
    j=[J(u) for u in range(total)]
    for a in inputs:
        left=responses[(a,0)]
        for b in outputs:
            right=responses[(0,b)]
            count[a,b]=sum(
                right[j[u]]==J(left[u]) for u in range(total))
    joined=round(time.monotonic()-start,4)
    # This comparison is an independent nine-round full-Feistel count.
    tbrute=time.monotonic()
    for a in inputs:
        for b in outputs:
            exact=direct(keys,a,b,nb,rot)
            assert count[a,b]==exact,(a,b,count[a,b],exact)
    brute=round(time.monotonic()-tbrute,4)
    result=dict(
        word_bits=w,endpoint_count=len(count),fixed_keys=list(keys),
        conditional_H_reused=True,shared_base_and_rotation_exact=True,
        cached_response_labels=len(responses),
        num_real_intermediate_bases=total,
        inverse_cache_seconds=t_inverse,
        prepared_seconds=prepare,
        total_cache_plus_joins_seconds=joined,
        independent_direct_all_cells_seconds=brute,
        exact_count_sum=sum(count.values()),
        zeros=sum(not v for v in count.values()),
        positives=sum(bool(v) for v in count.values()),
        speed_ratio_direct_over_cache=round(brute/joined,3) if joined else None,
        warning='toy full-base cache; impossible to materialize 2**64 labels')
    print('TWISTED_CONDITIONAL_CACHED_ALL_GATE_OK',
          json.dumps(result,sort_keys=True),flush=True)
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--nibbles',type=int,choices=(1,2),default=1)
    args=p.parse_args()
    if args.nibbles==1:
        out=run((5,6,7,8),1,1,range(1,16),range(1,16))
        assert (out['endpoint_count'],out['zeros'],out['positives'],
                out['exact_count_sum'])==(225,149,76,188)
    else:
        run((1,2,3,4),2,3,(1,),(1,0xd7,0x80,0xff))

if __name__=='__main__':main()
