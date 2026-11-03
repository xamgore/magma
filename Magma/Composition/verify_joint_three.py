#!/usr/bin/env python3
"""Independent full-state Z3 enumeration for GENERAL three-round RFC Magma DDT.

Cross-validates the generalized 3-g carry/tag Rust transfer, which
receives arbitrary input (aL,aR), output (bL,bR) and three fixed 32-bit
round keys. This solver does NOT impose the three-derivative equations
or use Rust transitions; it propagates two full 64-bit Feistel states
through exactly three ordinary rounds.

Every returned base is independently evaluated with the real Magma g,
then transformed into r=first g input and z=second g BASE input.
Only UNSAT after all pair-blocked models establishes an exact count.
"""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import g, BOX
sys.path.insert(0,str(Path(__file__).resolve().parent))
from opposite_five_fiber import feistel,z3_g_library

MASK=(1<<32)-1
DEFAULT_KEYS=(0x00002056,0xfdfa7789,0xf0f8d960)


def get_output(keys,base_left,base_right,delta_left,delta_right):
    l0,r0=feistel(keys,base_left,base_right)
    l1,r1=feistel(keys,base_left^delta_left,base_right^delta_right)
    return l0^l1,r0^r1


def count_three(keys,aL,aR,bL,bR,timeout_ms,max_models):
    from z3 import (BitVec,BitVecVal,Solver,Or,unsat,sat)
    G=z3_g_library()
    L=BitVec("three_input_L",32)
    R=BitVec("three_input_R",32)
    l0,r0=L,R
    l1,r1=L^BitVecVal(aL,32),R^BitVecVal(aR,32)
    for k in keys:
        K=BitVecVal(k,32)
        l0,r0=r0,l0^G(K,r0)
        l1,r1=r1,l1^G(K,r1)
    solver=Solver()
    solver.set(timeout=timeout_ms)
    solver.add((l0^l1)==BitVecVal(bL,32),
               (r0^r1)==BitVecVal(bR,32))
    started=time.monotonic()
    seen=set()
    witness_examples=[]
    status="unknown"
    for _ in range(max_models+1):
        c=solver.check()
        if c==unsat:
            status="complete_unsat_after_enumeration"
            break
        if c!=sat:
            status="unknown"
            break
        model=solver.model()
        xL=model.eval(L).as_long()
        xR=model.eval(R).as_long()
        assert get_output(keys,xL,xR,aL,aR)==(bL,bR)
        r=xR
        z=xL^g(keys[0],r)
        assert (r,z) not in seen
        seen.add((r,z))
        if len(witness_examples)<6:
            witness_examples.append(dict(
                plaintext=f"0x{xL:08x}{xR:08x}",
                r=f"0x{r:08x}",z=f"0x{z:08x}"))
        solver.add(Or(L!=BitVecVal(xL,32),R!=BitVecVal(xR,32)))
        if len(seen)%32==0:
            print("GENERAL_THREE_Z3_PROGRESS",len(seen),
                  round(time.monotonic()-started,2),flush=True)
    if len(seen)>max_models:
        status="model_cap"
    serialized="".join(f"{r:08x}{z:08x}\n" for r,z in sorted(seen))
    return dict(
       keys=[f"0x{k:08x}" for k in keys],
       input=[f"0x{aL:08x}",f"0x{aR:08x}"],
       output=[f"0x{bL:08x}",f"0x{bR:08x}"],
       status=status,
       count_or_lower_bound=len(seen),
       sha256_middle_bases=hashlib.sha256(serialized.encode()).hexdigest(),
       every_model_directly_replayed=True,
       first_solutions=witness_examples,
       seconds=round(time.monotonic()-started,3),
       limitation="UNKNOWN and model_cap do NOT prove exactness",
    )


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--keys",default="0x2056,0xfdfa7789,0xf0f8d960")
    p.add_argument("--input-left",type=lambda x:int(x,0),default=0x12345678)
    p.add_argument("--input-right",type=lambda x:int(x,0),default=0x9abcde12)
    p.add_argument("--output-left",type=lambda x:int(x,0))
    p.add_argument("--output-right",type=lambda x:int(x,0))
    p.add_argument("--seed-left",type=lambda x:int(x,0),default=0xf00d1234)
    p.add_argument("--seed-right",type=lambda x:int(x,0),default=0x12345678)
    p.add_argument("--timeout-ms",type=int,default=30000)
    p.add_argument("--model-cap",type=int,default=300)
    p.add_argument("--output",type=Path)
    c=p.parse_args()
    keys=tuple(int(k,0) for k in c.keys.split(","))
    assert len(keys)==3 and all(0<=x<=MASK for x in keys)
    aL,aR=c.input_left,c.input_right
    if c.output_left is None or c.output_right is None:
        assert c.output_left is None and c.output_right is None
        bL,bR=get_output(keys,c.seed_left,c.seed_right,aL,aR)
        print("GEN3_SEEDED_POSITIVE",json.dumps(dict(
            key_words=[f"0x{k:08x}" for k in keys],
            plaintext=f"0x{c.seed_left:08x}{c.seed_right:08x}",
            input=[f"0x{aL:08x}",f"0x{aR:08x}"],
            output=[f"0x{bL:08x}",f"0x{bR:08x}"]),sort_keys=True),flush=True)
    else:
        bL,bR=c.output_left,c.output_right
    report=count_three(keys,aL,aR,bL,bR,c.timeout_ms,c.model_cap)
    print("GENERAL_THREE_INDEPENDENT_Z3",json.dumps(report,sort_keys=True),flush=True)
    if c.output:
        c.output.parent.mkdir(parents=True,exist_ok=True)
        c.output.write_text(json.dumps(report,indent=2)+"\n")


if __name__=="__main__":
    main()
