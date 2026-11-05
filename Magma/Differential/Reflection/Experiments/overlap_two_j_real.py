#!/usr/bin/env python3
"""Exact lifted 3+3-overlap join for real 32-bit Magma, tested via #SMT.

Left J3=(k0,k1,k2), right J3=(k2,k3,k4), sharing the FULL
middle base state u after rounds k0,k1, its XOR difference delta,
and the output of their COMMON k2 round (base and difference).
Since the common round is a deterministic 0/1 constraint it is
not counted twice. Scalar three-round DDT matrices CANNOT replace
these lifted factors; overlap_two_j_probe.py has explicit examples.

This is an independent SMT check of the conditional-J mathematics,
NOT an efficient carryDP implementation. Counts are exact only
after blocked enumeration ends with UNSAT.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from Magma.Differential.FiveRounds.Experiments.opposite_five_fiber import (five_difference_conditions, middle_to_input,
                                 input_to_middle, feistel, z3_g_library)

KEYS=(0,0x2056,0xfdfa7789,0xf0f8d960,0)
KEYS_ALT=(0x12345678,0x2056,0xfdfa7789,0xf0f8d960,0x87654321)
CASES=(
  ("positive",KEYS,0x80000000,0x681e60a7,2,
   "120fb94a79c1f666068a50a105966b644d22810adf27457633cd198157a0e9e9"),
  ("unit_zero",KEYS,1,1,0,
   "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("strict_zero",KEYS,0x80000000,0x681e60a6,0,
   "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("nonzero_outer_keys",KEYS_ALT,0x80000000,0x1d43093d,8,
   "7d487edf13ac98c531b9b26dd0199f4a0f8f493c09b72b08949de28976f49733"),
)

def join_solver(keys,a,b,timeout_ms):
    from z3 import BitVec, BitVecVal, Solver
    G=z3_g_library()
    K=[BitVecVal(k,32) for k in keys]
    A=BitVecVal(a,32)
    B=BitVecVal(b,32)
    # Shared full state after the first two rounds.
    u=(BitVec("shared_base_left",32),BitVec("shared_base_right",32))
    delta=(BitVec("shared_diff_left",32),BitVec("shared_diff_right",32))
    up=(u[0]^delta[0],u[1]^delta[1])

    def fwd(s,k):
        l,r=s
        return (r,l^G(k,r))
    def backwards(s,k):
        l,r=s
        return (r^G(k,l),l)
    def dif(s,t):
        return (s[0]^t[0],s[1]^t[1])
    def three(s,kk):
        for k in kk:s=fwd(s,k)
        return s

    # LEFT conditional J3: reverse the first TWO rounds from the
    # shared state; its base and perturbed preimages must differ by
    # (0,a). The third round k2 is the shared overlap.
    original=backwards(backwards(u,K[1]),K[0])
    original_prime=backwards(backwards(up,K[1]),K[0])
    input_diff=dif(original,original_prime)

    # Shared central-round edge: both three-round windows see the
    # SAME actual base word u, the same delta and the same k2.
    central=fwd(u,K[2])
    central_prime=fwd(up,K[2])
    gamma=dif(central,central_prime)

    # RIGHT conditional J3: k2,k3,k4 from that same u and delta.
    after=three(u,K[2:])
    after_prime=three(up,K[2:])
    output_diff=dif(after,after_prime)
    s=Solver()
    s.set(timeout=timeout_ms)
    s.add(input_diff[0]==BitVecVal(0,32),
          input_diff[1]==A,
          output_diff[0]==B,
          output_diff[1]==BitVecVal(0,32))
    return s,u,delta,gamma

def exhaustive(keys,a,b,max_models=100,timeout_ms=15000):
    from z3 import Or,BitVecVal,sat,unsat
    solver,u,delta,gamma=join_solver(keys,a,b,timeout_ms)
    started=time.monotonic()
    points=[]
    status="UNKNOWN"
    for i in range(max_models+1):
        result=solver.check()
        if result==unsat:
            status="complete_unsat_after_enumeration"
            break
        if result!=sat:
            status="UNKNOWN"
            break
        model=solver.model()
        r,z=[model.eval(x).as_long() for x in u]
        p,q=[model.eval(x).as_long() for x in delta]
        gamma_pair=[model.eval(x).as_long() for x in gamma]
        good,trace=five_difference_conditions(keys,a,b,r,z)
        assert good,(r,z,a,b)
        assert (p,q)==(trace["p"],trace["q"]),("wrong shared diff",p,q,trace)
        assert gamma_pair==[q,trace["t"]],("wrong common round",gamma_pair,trace)
        x0,x1=middle_to_input(keys,r,z)
        assert input_to_middle(keys,x0,x1)==(r,z)
        base=feistel(keys,x0,x1)
        alternate=feistel(keys,x0,x1^a)
        assert (base[0]^alternate[0],base[1]^alternate[1])==(b,0)
        points.append((r,z))
        solver.add(Or(u[0]!=BitVecVal(r,32),u[1]!=BitVecVal(z,32)))
        if i+1>max_models:
            status="model_cap"
            break
    if len(points)>max_models:status="model_cap"
    assert len(set(points))==len(points)
    canonical="".join(f"{r:08x}{z:08x}\n" for r,z in sorted(points))
    return dict(status=status,count_or_lower_bound=len(points),
                hash=hashlib.sha256(canonical.encode()).hexdigest(),
                elapsed_s=round(time.monotonic()-started,3))

def main():
    cli=argparse.ArgumentParser()
    cli.add_argument("--timeout-ms",type=int,default=15000)
    cli.add_argument("--model-cap",type=int,default=100)
    args=cli.parse_args()
    for name,keys,a,b,expected,hash_expected in CASES:
        result=exhaustive(keys,a,b,args.model_cap,args.timeout_ms)
        assert result["status"]=="complete_unsat_after_enumeration",(name,result)
        assert result["count_or_lower_bound"]==expected,(name,result)
        assert result["hash"]==hash_expected,(name,result)
        print("REAL_LIFTED_TWO_J_AGREES",name,json.dumps(result,sort_keys=True),flush=True)
    print("REAL_LIFTED_TWO_J_GATE_OK",flush=True)

if __name__=="__main__":
    main()
