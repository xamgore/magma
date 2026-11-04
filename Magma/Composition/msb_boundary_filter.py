#!/usr/bin/env python3
"""Sound full-32-bit necessary filter for opposite five-round core.

When input a and output b are confined to the *highest* Magma
nibble, the real first/last g derivatives have key-independent
small exact S-box DDT supports. Enumerate these support sets
WITHOUT pretending their bases are independent; the center
three-round Feistel still uses the actual shared base words.

If NO (p,t) in the two outer support sets can be realized by
the TRUE central three-round fixed-key Feistel, then the whole
five-round core is impossible for that fixed key. An SAT
central witness is ONLY necessary, NOT a full-core witness.
UNKNOWN is never zero.

This is targeted 7-round compositional research, not a broad
nine-round SAT or a universal all-keys conclusion.
"""
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
sys.path.insert(0,str(ROOT/"Magma"/"Composition"))
from verify_nround import g
from opposite_five_fiber import z3_g_library, enumerate_core
from z3 import BitVec,BitVecVal,Or,Solver,sat,unsat

INNER=(0x2056,0xfdfa7789,0xf0f8d960)
OUTER=(0, *INNER, 0)
A=0x80000000

def support_top_nibble(d):
    assert d and (d&0x0fffffff)==0
    # lower 28 sum-input bits agree, so only Sbox #7 differs,
    # including for arbitrary full 32-bit keys.
    vals=set()
    for top in range(16):
        x=top<<28
        vals.add(g(0,x^d)^g(0,x))
    assert all(v and (v & ~0x780)==0 for v in vals)
    return sorted(vals)

def central(keys,a,b,timeout=10000):
    pchoices=support_top_nibble(a)
    tchoices=support_top_nibble(b)
    G=z3_g_library()
    x0,x1=BitVec("central_x0",32),BitVec("central_x1",32)
    p,t=BitVec("central_p",32),BitVec("central_t",32)
    bv=lambda v:BitVecVal(v,32)
    s=Solver()
    s.set(timeout=timeout)
    s.add(Or(*[p==bv(v) for v in pchoices]))
    s.add(Or(*[t==bv(v) for v in tchoices]))
    # Three TRUE linked Feistel derivative equations.
    x2=x0^G(bv(keys[0]),x1)
    q=bv(a)^G(bv(keys[0]),x1^p)^G(bv(keys[0]),x1)
    x3=x1^G(bv(keys[1]),x2)
    mid=p^G(bv(keys[1]),x2^q)^G(bv(keys[1]),x2)
    final=q^G(bv(keys[2]),x3^t)^G(bv(keys[2]),x3)
    s.add(mid==t,final==bv(b))
    started=time.monotonic()
    status=s.check()
    result=dict(status="SAT" if status==sat else
                "UNSAT" if status==unsat else "UNKNOWN",
                seconds=round(time.monotonic()-started,3),
                outer_p_support=[f"0x{v:08x}" for v in pchoices],
                outer_t_support=[f"0x{v:08x}" for v in tchoices],
                endpoint_a=f"0x{a:08x}",endpoint_b=f"0x{b:08x}",
                core_keys=[f"0x{v:08x}" for v in keys])
    if status==sat:
        m=s.model()
        result["sample_center"]={x:hex(m.eval(y).as_long()) for x,y
                                 in [('p',p),('t',t),('x0',x0),('x1',x1)]}
    if status==unsat:
        result["sound_fixed_key_five_core_zero"]=True
    return result

def main():
    for b in [0x80000000,0x10000000,0x40000000,0xf0000000]:
        result=central(INNER,A,b)
        print("MSB_BOUNDARY_CENTER_FILTER",
              json.dumps(result,sort_keys=True),flush=True)
    print("MSB_BOUNDARY_FILTER_GATE_END",flush=True)

if __name__=="__main__":main()
