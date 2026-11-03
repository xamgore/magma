#!/usr/bin/env python3
"""Third, truly seven-round full-state independent #SMT oracle.

No five-round boundary deletion or (r,z)-fiber reduction is used in
the SMT formula. Both 64-bit base states are propagated through
all seven *actual ordinary* RFC Magma rounds; fixed-key window 0..6
uses distinct master-key words 0..6.

Each result is independently replayed using research/verify_nround.py.
A bijective transformation extracts (r,z) only AFTER the solver
returns a model, to compare result-set hashes with the core solver.
Only UNSAT after complete model blocking makes the count exact.
"""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import rounds as direct_rounds
sys.path.insert(0,str(Path(__file__).resolve().parent))
from opposite_five_fiber import (
    feistel,ref_g,input_to_middle,five_difference_conditions,
    z3_g_library
)
MASK=0xffffffff

KEYS7=(0x12345678,0,0x00002056,0xfdfa7789,0xf0f8d960,0,0x87654321)


def independent_seven_count(keys7,a,b,timeout_ms,max_models):
    from z3 import BitVec,BitVecVal,Solver,Or,sat,unsat
    assert len(keys7)==7
    master=(*keys7,0xdeadbeef)
    G=z3_g_library()
    left=BitVec("outer7_left",32)
    right=BitVec("outer7_right",32)
    l0,r0=left,right
    l1,r1=left^BitVecVal(a,32),right
    for k in keys7:
        key=BitVecVal(k,32)
        l0,r0=r0,l0^G(key,r0)
        l1,r1=r1,l1^G(key,r1)
    s=Solver()
    s.set(timeout=timeout_ms)
    s.add(l0==l1, (r0^r1)==BitVecVal(b,32))
    seen=set()
    samples=[]
    started=time.monotonic()
    status="unknown"
    for count in range(max_models+1):
        result=s.check()
        if result==unsat:
            status="complete_unsat_after_enumeration"
            break
        if result!=sat:
            status="unknown"
            break
        model=s.model()
        L=model.eval(left).as_long()
        R=model.eval(right).as_long()
        X=(L<<32)|R
        Y=X^(a<<32)
        delta=direct_rounds(master,X,0,7)^direct_rounds(master,Y,0,7)
        assert delta==b,(hex(delta),hex(b))
        f0=feistel(keys7,L,R)
        f1=feistel(keys7,L^a,R)
        assert (f0[0]^f1[0], f0[1]^f1[1])==(0,b)
        inner_original_left=R
        inner_original_right=L^ref_g(keys7[0],R)
        r,z=input_to_middle(keys7[1:6],
                            inner_original_left,inner_original_right)
        good,_=five_difference_conditions(keys7[1:6],a,b,r,z)
        assert good
        assert (r,z) not in seen,(hex(r),hex(z))
        seen.add((r,z))
        if len(samples)<8:
            samples.append({
                "outer_base":f"0x{X:016x}",
                "inner_r":f"0x{r:08x}",
                "inner_z":f"0x{z:08x}",
            })
        s.add(Or(left!=BitVecVal(L,32),right!=BitVecVal(R,32)))
        if len(seen)%32==0:
            print("SEVEN_DIRECT_SMT_MODELS",len(seen),
                  round(time.monotonic()-started,2),flush=True)
    if len(seen)>max_models:
        status="model_cap"
    serialized="".join(f"{u:08x}{v:08x}\n" for u,v in sorted(seen))
    return dict(
        scope="seven RFC ordinary Feistel rounds, full 64-bit base, no 7->5 SMT shortcut",
        key_words=[f"0x{k:08x}" for k in master],
        keys7=[f"0x{k:08x}" for k in keys7],
        alpha=f"0x{a:08x}",
        beta=f"0x{b:08x}",
        status=status,
        count_or_lower_bound=len(seen),
        sha256_sorted_middle_bases=hashlib.sha256(serialized.encode()).hexdigest(),
        all_models_independently_replayed=True,
        first_models=samples,
        seconds=round(time.monotonic()-started,3)
    )


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--alpha",type=lambda x:int(x,0),default=0x80000000)
    p.add_argument("--beta",type=lambda x:int(x,0),default=0x681e60a7)
    p.add_argument("--keys7",default=None)
    p.add_argument("--timeout-ms",type=int,default=30000)
    p.add_argument("--model-cap",type=int,default=128)
    p.add_argument("--output",type=Path)
    cfg=p.parse_args()
    keys=KEYS7 if cfg.keys7 is None else tuple(int(x,0) for x in cfg.keys7.split(","))
    assert len(keys)==7 and all(0<=x<=MASK for x in keys)
    result=independent_seven_count(keys,cfg.alpha,cfg.beta,
                                   cfg.timeout_ms,cfg.model_cap)
    print("INDEPENDENT_REAL_7ROUND",json.dumps(result,sort_keys=True),flush=True)
    if cfg.output:
        cfg.output.parent.mkdir(parents=True,exist_ok=True)
        cfg.output.write_text(json.dumps(result,indent=2)+"\n")


if __name__=="__main__":
    main()
