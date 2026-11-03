#!/usr/bin/env python3
"""Key-schedule reflection spot check for the 8-round RFC Magma window 20..27.

An ordinary Feistel round G_k has inverse J G_k J, with J swapping
halves. For a palindromic sequence [k4,k5,k6,k7,k7,k6,k5,k4],
E8 satisfies E8^-1 = J E8 J. Therefore Q = J E8 is an involution;
in fact Q=H^-1 J H where H is its first four rounds.
As H is a permutation, Q has EXACTLY 2**32 fixed states for each key.

This is an algebraic *reflection* property, NOT an impossible
differential, nor a new cryptanalytic attack.
"""
import random
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from verify_nround import g, key_index

MASK=(1<<32)-1
def G(key,x):
    l,r=(x>>32)&MASK,x&MASK
    return (r<<32)|(l^g(key,r))

def inverseG(key,x):
    l,r=(x>>32)&MASK,x&MASK
    return ((r^g(key,l))<<32)|l

def J(x):
    return ((x&MASK)<<32)|((x>>32)&MASK)

def run(keys,x):
    for k in keys:x=G(k,x)
    return x

def inverse_run(keys,x):
    for k in reversed(keys):x=inverseG(k,x)
    return x

rng=random.Random(8891)
samples=0
for _ in range(24):
    master=[rng.getrandbits(32) for j in range(8)]
    seq=[master[key_index(i)] for i in range(20,28)]
    assert [key_index(i) for i in range(20,28)]==[4,5,6,7,7,6,5,4]
    assert seq==list(reversed(seq))
    H=seq[:4]
    for _ in range(100):
        x=rng.getrandbits(64)
        E=run(seq,x)
        Q=J(E)
        assert J(run(seq,Q))==x, 'Q is not an involution'
        assert inverse_run(seq,E)==x
        assert Q==inverse_run(H,J(run(H,x))), 'conjugation failed'
        t=rng.getrandbits(32)
        fixed_x=inverse_run(H,(t<<32)|t)
        assert J(run(seq,fixed_x))==fixed_x
        samples+=1
print('RFC_KEY_INDEX_SEQUENCE',list(map(lambda i:key_index(i),range(20,28))))
print('REFLECTION_CHECK_OK',samples,'random checks')
print('EXACT_FIXED_POINT_COUNT_FOR_EACH_MASTER',2**32)
print('STATUS: exact identity derived algebraically; independent Python spot-check only, not new Lean theorem')
