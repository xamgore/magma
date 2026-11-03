#!/usr/bin/env python3
"""Ablation of exact five-round (0,a)->(b,0) fiber correlations.

The Feistel right-difference stream is:
  d0=0, d1=a, d2=p, d3=q, d4=t, d5=b, d6=0
Five exact one-round derivative constraints require:
  Delta_g(k0,a,x1) = p
  Delta_g(k1,p,x2) = a XOR q
  Delta_g(k2,q,x3) = p XOR t
  Delta_g(k3,t,x4) = q XOR b
  Delta_g(k4,b,x5) = t

The *real* base recurrence adds three equalities:
  x1 = x3 XOR g(k1,x2)
  x4 = x2 XOR g(k2,x3)
  x5 = x3 XOR g(k3,x4).

Each weaker model drops some base equalities but retains the real
32-bit g derivative, key addition, carries and S-boxes. SAT in
a relaxation proves only a POSSIBLE local path; UNSAT in any
relaxation proves exact full-core UNSAT. This discovers which
correlation constraints actually prune.

No broad SAT matrices; targeted existing seven-round controls only.
"""
import argparse
import json
import time
from pathlib import Path

from opposite_five_fiber import (
    MASK,feistel,five_difference_conditions,middle_to_input,z3_g_library
)

ROOT=Path(__file__).resolve().parents[2]


def ablation(keys,a,b,timeout_ms):
    from z3 import BitVec, BitVecVal, Solver, sat, unsat
    assert len(keys)==5
    G=z3_g_library()
    K=[BitVecVal(k,32) for k in keys]
    A,B=BitVecVal(a,32),BitVecVal(b,32)
    p,q,t=[BitVec(x,32) for x in ("difference_p","difference_q","difference_t")]
    x=[BitVec(f"base_x{i}",32) for i in range(1,6)]
    base=Solver()
    base.set(timeout=timeout_ms)
    def gd(k,base,d):
        return G(k,base^d)^G(k,base)
    edges=[
        (gd(K[0],x[0],A),p),
        (gd(K[1],x[1],p),A^q),
        (gd(K[2],x[2],q),p^t),
        (gd(K[3],x[3],t),q^B),
        (gd(K[4],x[4],B),t),
    ]
    for lhs,rhs in edges:
        base.add(lhs==rhs)
    equalities={
        "mid":x[3]==x[1]^G(K[2],x[2]),
        "left":x[0]==x[2]^G(K[1],x[1]),
        "right":x[4]==x[2]^G(K[3],x[3]),
    }
    report=[]
    for model_name,links in [
        ("independent_local_5g",()),
        ("middle_base_coupled",("mid",)),
        ("middle_and_left_base",("mid","left")),
        ("fully_coupled_five_round",("mid","left","right")),
    ]:
        base.push()
        for name in links:
            base.add(equalities[name])
        begin=time.monotonic()
        response=base.check()
        duration=round(time.monotonic()-begin,3)
        entry=dict(model=model_name,
                   status="SAT" if response==sat else
                         "UNSAT" if response==unsat else "UNKNOWN",
                   seconds=duration,
                   added_base_links=list(links))
        if response==sat:
            m=base.model()
            values=[m.eval(v).as_long() for v in x]
            pval,qval,tval=(m.eval(v).as_long() for v in (p,q,t))
            entry["difference_trace"]=[
                f"0x{v:08x}" for v in (0,a,pval,qval,tval,b,0)]
            entry["base_words_x1_to_x5"]=[
                f"0x{v:08x}" for v in values]
            # Independent Python replay of ALL five local derivatives.
            from opposite_five_fiber import ref_g
            def gdreal(k,word,d):
                return ref_g(k,word^d)^ref_g(k,word)
            targets=(pval,a^qval,pval^tval,qval^b,tval)
            inputdiffs=(a,pval,qval,tval,b)
            assert all(gdreal(keys[i],values[i],inputdiffs[i])==targets[i]
                       for i in range(5))
            if "mid" in links:
                assert values[3]==values[1]^ref_g(keys[2],values[2])
            if "left" in links:
                assert values[0]==values[2]^ref_g(keys[1],values[1])
            if "right" in links:
                assert values[4]==values[2]^ref_g(keys[3],values[3])
            if len(links)==3:
                good,_=five_difference_conditions(
                    keys,a,b,values[1],values[2])
                assert good
            entry["all_constraints_independently_replayed"]=True
        if response not in (sat,unsat):
            entry["reason"]=base.reason_unknown()
        report.append(entry)
        print("OPPOSITE_ABLATION",json.dumps(entry,sort_keys=True),flush=True)
        base.pop()
    # Monotonicity is a strict logical property of these nested models.
    seen_unsat=False
    for item in report:
        if seen_unsat:
            assert item["status"]!="SAT",report
        seen_unsat|=item["status"]=="UNSAT"
    return report


def main():
    cli=argparse.ArgumentParser()
    cli.add_argument("--keys",default="0,0x2056,0xfdfa7789,0xf0f8d960,0")
    cli.add_argument("--alpha",type=lambda s:int(s,0),default=1)
    cli.add_argument("--beta",type=lambda s:int(s,0),default=1)
    cli.add_argument("--timeout-ms",type=int,default=20000)
    cli.add_argument("--output",type=Path)
    args=cli.parse_args()
    keys=tuple(int(v,0) for v in args.keys.split(","))
    assert len(keys)==5 and all(0<=x<=MASK for x in keys)
    answer=ablation(keys,args.alpha,args.beta,args.timeout_ms)
    result=dict(keys=[f"0x{v:08x}" for v in keys],
                alpha=f"0x{args.alpha:08x}",beta=f"0x{args.beta:08x}",
                models=answer,
                scope="Five exact independent round derivative supports with progressively restored Feistel base equality; necessary-only when not fully linked",
                caveat="SAT of a relaxation does not imply actual Feistel reachability; UNKNOWN does not mean UNSAT.")
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+"\n")


if __name__=="__main__":
    main()
