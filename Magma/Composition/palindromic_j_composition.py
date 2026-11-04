#!/usr/bin/env python3
"""RFC key reflection: J o G_rev o G and the nine-round outer DDT cut.

This is a structural identity and deterministic oracle, NOT a nine-round
search or a universal impossible-differential result. The key sequence
rounds 20..28 is [4,5,6,7,7,6,5,4,3], so its first eight are a
palindrome. G is its first 4 rounds and G_rev its reversed 4 rounds.
Thus Q = J o G_rev o G = G^{-1} o J o G and Q^2 = identity.
The final 9th round can be removed from the (0,b) output slice:
D9((a,0),(0,b)) = D8((a,0),(b,0)) = D_Q((a,0),(0,b)).
"""
import json
import random
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import g,key_index

M=(1<<32)-1

def F(k,x):
    l,r=x
    return r,l^g(k,r)

def invF(k,y):
    l,r=y
    return r^g(k,l),l

def apply(keys,x):
    for k in keys:x=F(k,x)
    return x

def inverse(keys,y):
    for k in keys[::-1]:y=invF(k,y)
    return y

def J(x):
    return x[1],x[0]

def xor(a,b):
    return a[0]^b[0],a[1]^b[1]

def main():
    rng=random.Random(0x889133)
    schedule=[key_index(i) for i in range(20,29)]
    assert schedule==[4,5,6,7,7,6,5,4,3],schedule
    checked=0
    for sample in range(16):
        master=[rng.getrandbits(32) for _ in range(8)]
        first4=[master[i] for i in schedule[:4]]
        mirror=[master[i] for i in schedule[4:8]]
        eight=first4+mirror
        nine=eight+[master[schedule[8]]]
        assert mirror==first4[::-1]
        for _ in range(80):
            x=(rng.getrandbits(32),rng.getrandbits(32))
            alpha=(rng.getrandbits(32),rng.getrandbits(32))
            b=(rng.getrandbits(32),rng.getrandbits(32))
            revG=apply(mirror,apply(first4,x))
            q=J(revG)
            assert q==inverse(first4,J(apply(first4,x)))
            assert J(apply(eight,q))==x
            # Full 9-round DDT postimage fixed to (0,b) forces the
            # output difference of 8-round prefix to (b,0), exactly.
            z=apply(eight,x)
            zp=apply(eight,xor(x,alpha))
            out8=xor(z,zp)
            out9=xor(apply(nine,x),apply(nine,xor(x,alpha)))
            for target in (0,1,0x80000000,b[0]):
                assert (out9==(0,target)) == (out8==(target,0))
            # Q output difference is J(out8).
            assert xor(q,J(zp))==J(out8)
            checked+=1
    print("PALINDROMIC_J_REV_G_FORWARD_G_OK",json.dumps(dict(
        checked_pairs=checked,checked_masters=16,
        nine_window_key_indices=schedule,
        eight_palindrome=True,
        identity="Q = J o G_rev o G = inverse(G) o J o G",
        involution=True,
        one_sided_9_to_8_ddt_reduction=True,
        caveat="Does not establish universal impossible differentials."
    ),sort_keys=True),flush=True)

if __name__=="__main__":
    main()
