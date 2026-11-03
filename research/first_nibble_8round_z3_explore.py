#!/usr/bin/env python3
"""Experimental *necessary* first-active-nibble constraints on 8-round outer DDT.

Full eight-round outer (a,0)->(0,s) is an exact six-round inner
(0,a)->(s,0). Encode the six consecutive Feistel derivatives
with four abstract intermediate word differences p,q,r,t:

(d0,d1,d2,d3,d4,d5,d6,d7)=(0,a,p,q,r,t,s,0).

At each edge the nonrotated derivative of the round function has
the same least active 4-bit digit as its XOR input difference.
This omits S-box/carry/base compatibility and is therefore a SOUND
necessary overapproximation of real reachability.
"""
from z3 import *
import json
import subprocess
import time
from pathlib import Path

def first_nibble_necessary(src, out):
    rotated = RotateRight(out,11)
    return [((src & BitVecVal((1<<(4*i))-1,32)) == 0)
            == ((rotated & BitVecVal((1<<(4*i))-1,32)) == 0)
            for i in range(1,9)]

p,q,r,t=[BitVec(x,32) for x in ('p','q','r','t')]
def formula(a,s):
    delta=[BitVecVal(0,32),BitVecVal(a,32),p,q,r,t,BitVecVal(s,32),BitVecVal(0,32)]
    return [expr for i in range(6)
            for expr in first_nibble_necessary(delta[i+1],delta[i]^delta[i+2])]

def check_rep(i,j,timeout=5000):
    sl=Solver();sl.set('timeout',timeout)
    sl.add(formula(1<<i,1<<j))
    start=time.monotonic();res=sl.check()
    print(f'input_bit={i:02} output_bit={j:02} first_nibble={res} seconds={time.monotonic()-start:.3f}',
          flush=True)
    if res==sat:
        m=sl.model()
        print('P,Q,R,T',[hex(m[x].as_long()) for x in (p,q,r,t)],flush=True)
    return res

if __name__=='__main__':
    for i,j in [(20,28),(24,28),(28,20),(28,24),(28,28),(0,0),(12,18),(20,24),(24,24)]:
        check_rep(i,j)
