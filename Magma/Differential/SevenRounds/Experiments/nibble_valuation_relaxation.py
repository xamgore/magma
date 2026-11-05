#!/usr/bin/env python3
"""Key-independent 2-adic nibble-valuation relaxation for Magma g.

For nonzero XOR difference d, the first nonzero 4-bit nibble
is unchanged by fixed-key modular addition (the FIRST differing
bit is preserved), and each RFC S-box is a bijection. Therefore
the first nonzero input nibble index equals the first nonzero
nibble index of rotateRight11(gDelta). This is a NECESSARY,
not sufficient, differential relation for ANY independent keys.

Targeted 7/9-round tests here solve ONLY this difference-level
relaxation; no Magma g, key, or real base variables are put in
Z3. A completed UNSAT is a universal impossible-differential
certificate after formally proving the nibble rule; SAT is only
a spurious-relaxation candidate.

Not a bulk nine-round cryptanalytic search.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse,json,time
from z3 import BitVec,BitVecVal,RotateRight,Or,And,Solver,sat,unsat

MASK=(1<<32)-1
def low_nibble_pred(d,i):
    lower=(1<<(4*i))-1
    return And((d & BitVecVal(lower,32))==BitVecVal(0,32),
               (d & BitVecVal(15<<(4*i),32))!=BitVecVal(0,32))

def relation(d,e):
    r=RotateRight(e,11)
    return Or(And(d==BitVecVal(0,32),e==BitVecVal(0,32)),
              Or(*[And(low_nibble_pred(d,i),low_nibble_pred(r,i))
                   for i in range(8)]))

def probe(rounds,a,b,timeout=15000):
    assert rounds>=3
    d=[BitVecVal(0,32),BitVecVal(a,32)]
    d.extend(BitVec("diff%d"%i,32) for i in range(2,rounds))
    d.extend([BitVecVal(b,32),BitVecVal(0,32)])
    assert len(d)==rounds+2
    s=Solver()
    s.set(timeout=timeout)
    for i in range(rounds):
        s.add(relation(d[i+1],d[i]^d[i+2]))
    t=time.monotonic()
    status=s.check()
    result=dict(core_rounds=rounds,outer_rounds=rounds+2,
                a=f"0x{a:08x}",b=f"0x{b:08x}",
                status="UNSAT" if status==unsat else "SAT" if status==sat else "UNKNOWN",
                seconds=round(time.monotonic()-t,3))
    if status==sat:
        m=s.model()
        result["relaxed_stream"]=[f"0x{m.eval(v).as_long():08x}" for v in d]
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--timeout",type=int,default=15000)
    args=parser.parse_args()
    for rounds,a,b in [
      (5,0x80000000,0x80000000),
      (6,0x80000000,0x80000000),
      (7,0x80000000,0x80000000),
      (7,0x10000000,0x10000000),
      (7,0x80000000,0x10000000),
      (7,0x80000000,0x80000001),
    ]:
        r=probe(rounds,a,b,args.timeout)
        print("NIBBLE_VALUATION_RELAXATION",json.dumps(r,sort_keys=True),flush=True)

if __name__=="__main__":main()
