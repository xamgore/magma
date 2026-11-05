#!/usr/bin/env python3
"""Research: two overlapping 3-round J kernels versus genuine 5-round DDT.

A 4-bit-word Feistel toy uses the RFC first S-box and rotl1. Each of its
five Feistel rounds is invertible. This small model permits exhaustive
counting and shows which *full-state* labels are indispensable for 3+3
(overlap in one round). It is NOT a new RFC 32-bit DDT solver.

The scalar DDT product is a deliberately INVALID independence proxy,
reported as a counterexample, NEVER as a correct five-round count.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX

W=4
MASK=(1<<W)-1
N=1<<(2*W)
KEYS=(1,2,3,4,5)

def g(key,x):
    q=BOX[0][(key+x)&MASK]
    return ((q<<1)|(q>>3))&MASK

def rd(state,key):
    l,r=state
    return (r,l^g(key,r))

def rinverse(state,key):
    l,r=state
    return (r^g(key,l),l)

def fw(state,keys):
    for key in keys: state=rd(state,key)
    return state

def inv(state,keys):
    for key in reversed(keys):state=rinverse(state,key)
    return state

def xor(u,v):
    return (u[0]^v[0],u[1]^v[1])

def encode(v):
    return (v[0]<<W)|v[1]

def decode(i):
    return (i>>W,i&MASK)

def differential(state,d,keys):
    return xor(fw(state,keys),fw(xor(state,d),keys))

def ddt(keys):
    arr=[[0]*N for _ in range(N)]
    for ia in range(N):
        delta=decode(ia)
        for x in range(N):
            u=decode(x)
            arr[ia][encode(differential(u,delta,keys))]+=1
    return arr

def exact_overlap(keys,alpha,beta):
    """Two 3-round *lifted* J checks, sharing pre/post k2 real state.

    Left J=(k0,k1,k2), right J=(k2,k3,k4). The first 3-block output
    state is round(k2,u), where u is state after k0,k1. Its difference
    equals round(k2, u^delta) XOR round(k2,u). Hence k2 is counted ONCE.
    """
    count=0
    for iu in range(N):
        u=decode(iu)
        x=inv(u,keys[:2])
        xprime=xor(x,alpha)
        uprime=fw(xprime,keys[:2])
        delta=xor(u,uprime)
        v=rd(u,keys[2])
        gamma=xor(v,rd(uprime,keys[2]))
        assert differential(x,alpha,keys[:3])==gamma
        assert differential(u,delta,keys[2:3])==gamma
        if differential(u,delta,keys[2:])==beta:
            count+=1
    return count

def naive_marginal_double_j(left,one,right,alpha,beta):
    """Unjustified independence: sum_delta,gamma L3 * R1 * R3 / N^2."""
    ia,ib=encode(alpha),encode(beta)
    total=0
    for j in range(N):
        rightmass=right[j][ib]
        if not rightmass:continue
        row=one[j]
        for k,centralmass in enumerate(row):
            if centralmass:
                total+=left[ia][k]*centralmass*rightmass
    return total,N*N

def main():
    started=time.monotonic()
    left=ddt(KEYS[:3])
    central=ddt(KEYS[2:3])
    right=ddt(KEYS[2:])
    completed=ddt(KEYS)
    reverse=ddt(tuple(reversed(KEYS)))
    # F_K^{-1} = swap o F_reverse(K) o swap. Inverse-DDT
    # transposes input/output differences but does NOT turn the
    # opposite orientation into the outer orientation.
    for ia in range(N):
        a=decode(ia)
        for ib in range(N):
            b=decode(ib)
            assert completed[ia][ib]==reverse[
                encode((b[1],b[0]))][encode((a[1],a[0]))]
    for p in range(N):
        assert sum(left[p])==N
        assert sum(right[p])==N

    sample=[]
    counterexamples=[]
    for a in range(1,16):
        for b in range(1,16):
            alpha=(0,a)
            beta=(b,0)
            real=completed[encode(alpha)][encode(beta)]
            exact=exact_overlap(KEYS,alpha,beta)
            assert exact==real,(alpha,beta,real,exact)
            num,den=naive_marginal_double_j(left,central,right,alpha,beta)
            if num!=real*den:
                counterexamples.append(dict(a=a,b=b,exact=real,
                   marginal_num=num,marginal_den=den,
                   marginal_positive=num>0))
            if real and len(sample)<6:
                sample.append(dict(a=a,b=b,exact=real,
                                   naive_num=num,naive_den=den))
    assert counterexamples, "expected a mismatch; no independence proof exists"
    wrong_zeros=[c for c in counterexamples
                 if c["exact"]==0 and c["marginal_positive"]]
    zero_count=sum(completed[encode((0,a))][encode((b,0))]==0
                   for a in range(1,16) for b in range(1,16))

    # The zero propagation law is a consequence of bijective g.
    for key in range(16):
        for x in range(16):
            for d in range(16):
                gd=g(key,x^d)^g(key,x)
                assert (gd==0)==(d==0)
    # Check the same law at every round for every complete toy trace.
    for state_id in range(N):
        state=decode(state_id)
        for a in range(1,16):
            alternate=xor(state,(0,a))
            d0,d1=0,a
            s=state
            t=alternate
            for key in KEYS:
                s,t=rd(s,key),rd(t,key)
                d2=xor(s,t)[1]
                assert (d2==d0)==(d1==0)
                d0,d1=d1,d2

    result=dict(
        scope="4-bit toy S-box, NOT full RFC Magma",
        states=N,
        keys=list(KEYS),
        checked_endpoints=225,
        true_zero_endpoints=zero_count,
        exact_overlapping_lifted_J_matches_bruteforce=True,
        inverse_reverse_key_DDT_symmetry_checked=True,
        naive_DDT_only_mismatches=len(counterexamples),
        naive_false_positive_zero_endpoints=len(wrong_zeros),
        representative_false_positive=wrong_zeros[0] if wrong_zeros else None,
        representative_other_mismatch=counterexamples[0],
        positive_samples=sample,
        checked_g_bijectivity_and_zero_rule=True,
        elapsed_seconds=round(time.monotonic()-started,3))
    print("OVERLAP_TWO_J_RESULT",json.dumps(result,sort_keys=True),flush=True)
    assert result["naive_DDT_only_mismatches"]>0
    print("OVERLAP_TWO_J_GATE_OK",flush=True)

if __name__=="__main__":
    main()
