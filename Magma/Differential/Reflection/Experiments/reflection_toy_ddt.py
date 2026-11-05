#!/usr/bin/env python3
"""Exhaustive 4-bit-word Feistel reflection count, not RFC full-width Magma.

Verifies exact equality D9_outer = D8_palindrome = D_Q using a toy key
schedule [4,5,6,7,7,6,5,4,3] and RFC first S-box with rotl1. Verifies
the independent crossed-four-round G constraint, keeping complete
base-state correlations. Reports observed zero/positive endpoint counts;
toy counts are not universal differential theorems.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from Magma.Differential.Reflection.Experiments.overlap_two_j_probe import fw,inv,decode,xor,encode
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy

KEYS=(5,6,7,8,8,7,6,5,4)
A=KEYS[:4]
M=15

def J(p):return p[1],p[0]

def palindrome(p):
    return feistel_toy(KEYS[:8],p[0],p[1],1,1)

def nine(p):
    return feistel_toy(KEYS,p[0],p[1],1,1)

def G(p):
    return feistel_toy(A,p[0],p[1],1,1)

def inverse_G(p):
    # Feistel round inverse with same 4-bit RFC g
    from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import g_toy
    l,r=p
    for k in A[::-1]:
        l,r=(r^g_toy(k,l,1,1),l)
    return l,r

def Q(p):
    return J(palindrome(p))

def main():
    t=time.monotonic()
    for i in range(256):
        x=decode(i)
        assert Q(x)==inverse_G(J(G(x)))
        assert Q(Q(x))==x
    zeros=0
    positives=0
    witness_count=0
    for a in range(1,16):
        alpha=(a,0)
        for b in range(1,16):
            beta=(0,b)
            count9=count8=countQ=cross=0
            for i in range(256):
                x=decode(i)
                xprime=xor(x,alpha)
                count9+=xor(nine(x),nine(xprime))==beta
                count8+=xor(palindrome(x),palindrome(xprime))==(b,0)
                countQ+=xor(Q(x),Q(xprime))==beta
                # Two copies of G must share a *real* reflected base.
                y=inverse_G(J(G(x)))
                cross+=G(xor(y,beta))==J(G(xprime))
            assert count9==count8==countQ==cross,(a,b,count9,count8,countQ,cross)
            zeros+=count9==0
            positives+=count9>0
            witness_count+=count9
    print("REFLECTION_TOY_DDT_GATE_OK",json.dumps(dict(
        toy_word_bits=4,
        endpoint_pairs=225,
        zero_coefficients=zeros,
        positive_coefficients=positives,
        sum_selected_coefficients=witness_count,
        identity="D9(alpha,(0,b))=D8(alpha,(b,0))=D_Q(alpha,(0,b))",
        crossed_four_round_join_exact=True,
        elapsed_s=round(time.monotonic()-t,3),
        warning="toy-only; no 32-bit DDT or key-universal impossibility conclusion"
    ),sort_keys=True),flush=True)

if __name__=="__main__":
    main()
