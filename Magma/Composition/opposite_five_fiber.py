#!/usr/bin/env python3
"""Exact five-round opposite-orientation fiber and seven-round outer reduction.

The *unsolved* 5-round core required by the proved 7->5 boundary identity:
  ((0,a) -> (b,0)) over ordinary Feistel rounds.

An exact 64-bit base-state bijection uses r=x2, z=x3 (the
right-word Feistel sequence). Then:
    x1 = z XOR g(k1,r)
    x0 = r XOR g(k0,x1)
and x4,x5,x6 follow deterministically.

The code defines five genuinely correlated g derivatives over
(r,z), and checks them against a SECOND, DIRECT Feistel SMT model
with free original plaintext (x0,x1). Completed model enumerations
must reach UNSAT. UNKNOWN/timeout never means impossible.

No invented orientation equivalence to (a,0)->(0,b).
No extra Lean proof, no nine-round SAT sweep.
"""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX,g as ref_g

MASK=0xffffffff


def feistel(keys,left,right):
    for k in keys:
        left,right=right,(left^ref_g(k,right))&MASK
    return left,right


def middle_to_input(keys,r,z):
    x1=z^ref_g(keys[1],r)
    x0=r^ref_g(keys[0],x1)
    return x0,x1


def input_to_middle(keys,x0,x1):
    x2=x0^ref_g(keys[0],x1)
    x3=x1^ref_g(keys[1],x2)
    return x2,x3


def five_difference_conditions(keys,a,b,r,z):
    k0,k1,k2,k3,k4=keys
    x0,x1=middle_to_input(keys,r,z)
    assert input_to_middle(keys,x0,x1)==(r,z)
    gdiff=lambda k,d,x:ref_g(k,x^d)^ref_g(k,x)
    p=gdiff(k0,a,x1)
    q=a^gdiff(k1,p,r)
    x4=r^ref_g(k2,z)
    t=p^gdiff(k2,q,z)
    v=q^gdiff(k3,t,x4)
    x5=z^ref_g(k3,x4)
    w=t^gdiff(k4,v,x5)
    passed=(v==b and w==0)
    first=feistel(keys,x0,x1)
    second=feistel(keys,x0,x1^a)
    assert (first[0]^second[0],first[1]^second[1])==(v,w)
    return passed,dict(p=p,q=q,t=t,v=v,w=w,
                       x0=x0,x1=x1,x4=x4,x5=x5)


def seven_outer_checks(keys7,a,b,r,z):
    assert len(keys7)==7
    k5=keys7[1:6]
    x0,x1=middle_to_input(k5,r,z)
    # 7-round initial plaintext chosen so its state after the first
    # round has base (x0,x1) and input diff (0,a).
    # First-round mapping: (L0,R0)->(R0,L0 XOR g(k0,R0))
    R0=x0
    L0=x1^ref_g(keys7[0],R0)
    initial=feistel(keys7,L0,R0)
    alternate=feistel(keys7,L0^a,R0)
    assert (initial[0]^alternate[0],initial[1]^alternate[1])==(0,b),       (hex(initial[0]^alternate[0]),hex(initial[1]^alternate[1]),hex(b))


def z3_g_library():
    from z3 import (BitVecVal,Concat,Extract,LShR,RotateLeft,ZeroExt)
    lookup=[sum(int(v)<<(4*j) for j,v in enumerate(box)) for box in BOX]
    def G(k,x):
        t=k+x
        substituted=Concat(*[
            Extract(3,0,LShR(BitVecVal(lookup[i],64),
                ZeroExt(60,Extract(4*i+3,4*i,t)) << 2))
            for i in range(7,-1,-1)
        ])
        return RotateLeft(substituted,11)
    return G


def make_solver(keys,a,b,method,timeout_ms):
    from z3 import BitVec,BitVecVal,Solver
    G=z3_g_library()
    K=[BitVecVal(x,32) for x in keys]
    A,B=BitVecVal(a,32),BitVecVal(b,32)
    s=Solver()
    s.set(timeout=timeout_ms)
    if method=="middle":
        r,z=BitVec("middle_r",32),BitVec("middle_z",32)
        x1=z^G(K[1],r)
        p=G(K[0],x1^A)^G(K[0],x1)
        q=A^(G(K[1],r^p)^G(K[1],r))
        x4=r^G(K[2],z)
        t=p^(G(K[2],z^q)^G(K[2],z))
        v=q^(G(K[3],x4^t)^G(K[3],x4))
        x5=z^G(K[3],x4)
        w=t^(G(K[4],x5^v)^G(K[4],x5))
        s.add(v==B,w==BitVecVal(0,32))
        return s,(r,z)
    if method=="direct":
        left,right=BitVec("original_left",32),BitVec("original_right",32)
        left2,right2=left,right^A
        for k in K:
            left,right=right,left^G(k,right)
            left2,right2=right2,left2^G(k,right2)
        s.add((left^left2)==B,(right^right2)==BitVecVal(0,32))
        return s,(BitVec("original_left",32),BitVec("original_right",32))
    raise ValueError(method)


def enumerate_core(keys,a,b,method,timeout_ms,max_models,early_check=None):
    from z3 import BitVecVal,Or,sat,unsat
    s,variables=make_solver(keys,a,b,method,timeout_ms)
    started=time.monotonic()
    solutions=[]
    status="unknown"
    for idx in range(max_models+1):
        result=s.check()
        if result==unsat:
            status="complete_unsat_after_enumeration"
            break
        if result!=sat:
            status="unknown"
            break
        model=s.model()
        u,v=[model.eval(var).as_long() for var in variables]
        if method=="middle":
            r,z=u,v
            x0,x1=middle_to_input(keys,r,z)
            good,trace=five_difference_conditions(keys,a,b,r,z)
            assert good
        else:
            x0,x1=u,v
            r,z=input_to_middle(keys,x0,x1)
            good,trace=five_difference_conditions(keys,a,b,r,z)
            assert good
        assert (feistel(keys,x0,x1)[0]^feistel(keys,x0,x1^a)[0],
                feistel(keys,x0,x1)[1]^feistel(keys,x0,x1^a)[1])==(b,0)
        solutions.append((r,z))
        s.add(Or(variables[0]!=BitVecVal(u,32),
                 variables[1]!=BitVecVal(v,32)))
        if early_check:
            early_check(r,z)
        if (idx+1)%32==0:
            print("OPPOSITE_CORE_PROGRESS",method,idx+1,
                  round(time.monotonic()-started,2),flush=True)
    if len(solutions)>max_models:
        status="model_cap"
    unique=set(solutions)
    assert len(unique)==len(solutions)
    text="".join(f"{r:08x}{z:08x}\n" for r,z in sorted(unique))
    return {
        "method":method,
        "status":status,
        "count_or_lower_bound":len(solutions),
        "sha256_sorted_middle_bases":hashlib.sha256(text.encode()).hexdigest(),
        "seconds":round(time.monotonic()-started,3),
        "sample_pairs":[[f"0x{r:08x}",f"0x{z:08x}"] for r,z in sorted(unique)[:8]]
    }


def discover_positive(keys,a,timeout_ms):
    """Find beta from a REAL right-output-zero Feistel pair, not guess it.

    The beta word is an unconstrained output of the SAT model.
    Output: discovered beta, concrete 64-bit input base, and a
    middle-base pair which independently replays the 5-round path.
    """
    from z3 import BitVec,BitVecVal,Solver,sat
    G=z3_g_library()
    K=[BitVecVal(k,32) for k in keys]
    A=BitVecVal(a,32)
    l,r=BitVec("discover_left",32),BitVec("discover_right",32)
    l2,r2=l,r^A
    for k in K:
        l,r=r,l^G(k,r)
        l2,r2=r2,l2^G(k,r2)
    solver=Solver()
    solver.set(timeout=timeout_ms)
    solver.add(r==r2)
    # Must be a nonzero endpoint (Feistel is a permutation for any key).
    solver.add((l^l2)!=BitVecVal(0,32))
    check=solver.check()
    if check!=sat:
        return dict(status=str(check),reason=solver.reason_unknown())
    m=solver.model()
    x0=m.eval(BitVec("discover_left",32)).as_long()
    x1=m.eval(BitVec("discover_right",32)).as_long()
    b=m.eval(l^l2).as_long()
    assert b!=0
    p0=feistel(keys,x0,x1)
    p1=feistel(keys,x0,x1^a)
    assert (p0[0]^p1[0],p0[1]^p1[1])==(b,0)
    r0,z0=input_to_middle(keys,x0,x1)
    good,_=five_difference_conditions(keys,a,b,r0,z0)
    assert good
    return dict(status="sat",alpha=f"0x{a:08x}",
                discovered_beta=f"0x{b:08x}",
                original_left=f"0x{x0:08x}",
                original_right=f"0x{x1:08x}",
                middle_r=f"0x{r0:08x}",middle_z=f"0x{z0:08x}")


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--alpha",type=lambda x:int(x,0),default=0x00000001)
    p.add_argument("--beta",type=lambda x:int(x,0),default=0x00000001)
    p.add_argument("--keys",default="0x0,0x2056,0xfdfa7789,0xf0f8d960,0x0")
    p.add_argument("--mode",choices=["middle","direct","both"],default="both")
    p.add_argument("--timeout-ms",type=int,default=15000)
    p.add_argument("--model-cap",type=int,default=1000)
    p.add_argument("--seven-outer",action="store_true")
    p.add_argument("--discover-positive",action="store_true")
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    keys=tuple(int(v,0) for v in args.keys.split(","))
    assert len(keys)==5
    assert all(0<=v<=MASK for v in keys)
    a,b=args.alpha,args.beta
    assert 0<=a<=MASK and 0<=b<=MASK
    discovered=None
    if args.discover_positive:
        discovered=discover_positive(keys,a,args.timeout_ms)
        print("OPPOSITE_DISCOVERY",json.dumps(discovered,sort_keys=True),flush=True)
        if discovered["status"]!="sat":
            return dict(discovery=discovered,status="UNKNOWN")
        b=int(discovered["discovered_beta"],16)
    keys7=(0x12345678,*keys,0x87654321)
    checker=(lambda r,z:seven_outer_checks(keys7,a,b,r,z)) if args.seven_outer else None
    modes=("middle","direct") if args.mode=="both" else (args.mode,)
    results=[]
    for method in modes:
        result=enumerate_core(keys,a,b,method,args.timeout_ms,args.model_cap,checker)
        results.append(result)
        print("OPPOSITE_CORE_SOLVER",json.dumps(result,sort_keys=True),flush=True)
    if len(results)==2 and all(t["status"]=="complete_unsat_after_enumeration" for t in results):
        assert results[0]["count_or_lower_bound"]==results[1]["count_or_lower_bound"]
        assert results[0]["sha256_sorted_middle_bases"]==results[1]["sha256_sorted_middle_bases"]
        print("INDEPENDENT_OPPOSITE_CORE_ENUMERATION_IDENTICAL",results[0]["count_or_lower_bound"],flush=True)
    report=dict(
        input_5core=[f"0x{0:08x}",f"0x{a:08x}"],
        output_5core=[f"0x{b:08x}",f"0x{0:08x}"],
        input_7outer=[f"0x{a:08x}",f"0x{0:08x}"],
        output_7outer=[f"0x{0:08x}",f"0x{b:08x}"],
        keys_5=[f"0x{x:08x}" for x in keys],
        keys_7=[f"0x{x:08x}" for x in keys7],
        methods=results,
        discovery=discovered,
        formal_status="kernel-proved 7->5 boundary count identity in FirstRoundDeletion.lean; computational opposite-core counts",
        note="Fixed-key counts ONLY, not universal 7-round impossible differences."
    )
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2)+"\n")
    return report


if __name__=="__main__":
    main()
