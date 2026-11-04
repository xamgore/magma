#!/usr/bin/env python3
"""Verify the assumed RFC Magma g permutation implementation.

The *proof* of no nonzero zero-output derivatives is algebraic:
each RFC 4-bit S-box is a permutation; fixed-key modular addition
and rotate-left-11 are bijections. Deterministic random checks below
are regression tests of the independently written inverse, NOT a
substitute for that mathematical argument.
"""
import json
import random
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX,g

MASK=(1<<32)-1
INV=[]
for box in BOX:
    assert sorted(box)==list(range(16)), "RFC S-box is not bijective"
    inv=[0]*16
    for x,y in enumerate(box): inv[y]=x
    INV.append(inv)

def ginverse(key,output):
    sb=((output>>11)|(output<<21))&MASK
    pre_add=sum(INV[i][(sb>>(4*i))&15]<<(4*i) for i in range(8))
    return (pre_add-key)&MASK

def main():
    rng=random.Random(0x5A111)
    checks=0
    for key in (0,0x2056,0xfdfa7789,0xf0f8d960,0x87654321,
                0xffffffff,0x80000000):
        for j in range(256):
            x=rng.getrandbits(32)
            d=rng.getrandbits(32) or 1
            y=g(key,x)
            assert ginverse(key,y)==x
            assert g(key,ginverse(key,y))==y
            assert g(key,x^d)!=y
            checks+=1
    print("MAGMA_G_PERMUTATION_GATE_OK",
          json.dumps(dict(sboxes=8,tests=checks,
                          inverse_algebra="ror11 + inverse 4-bit S-boxes + modular subtraction",
                          zero_derivative_iff_input_zero=True)),flush=True)

if __name__=="__main__":
    main()
