#!/usr/bin/env python3
"""Independent #SMT verifier for FULL five-round outer Magma DDT counts.

The Rust joint carry-DP is NOT imported here. Z3 models two freely
varying 32-bit bases r,z and three fixed RFC 8891 Magma subkeys.
Every satisfying pair is reified to a concrete five-round Feistel
plaintext, and its XOR output is directly evaluated by independent
Python Magma g, then model-blocked. Solver UNSAT after all models
makes the integer count exact. UNKNOWN/time cap is never called zero.

Run:
  python3 Magma/Differential/FiveRounds/Experiments/verify_joint_full_z3.py \
      --fixture 0 --expected 768 --timeout-ms 60000
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

ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX,g

MASK=(1<<32)-1
CASES=[
    dict(name="one-hot-to-four-hot",
         keys=(0,0x00002056,0xfdfa7789,0xf0f8d960,0),
         alpha=0x00000080,beta=0xc0000820),
    dict(name="two-hot-to-three-hot",
         keys=(0,0xb3900250,0xddfc38c3,0xca24f050,0),
         alpha=0x80000080,beta=0x20200020),
]


def five_round(keys,x):
    left=(x>>32)&MASK
    right=x&MASK
    for k in keys:
        left,right=right,left^g(k,right)
    return (left<<32)|right


def exact_enumeration(fixture,expected,timeout_ms,model_cap,output):
    from z3 import (BitVec,BitVecVal,Concat,Extract,LShR,RotateLeft,
                    ZeroExt,Solver,Or,unsat,sat)
    lut=[sum(int(value)<<(4*j) for j,value in enumerate(row)) for row in BOX]
    def G(k,x):
        x=k+x
        substituted=Concat(*[
            Extract(3,0,LShR(BitVecVal(lut[i],64),
                ZeroExt(60,Extract(4*i+3,4*i,x)) << 2))
            for i in range(7,-1,-1)
        ])
        return RotateLeft(substituted,11)

    keys=fixture["keys"]
    k1,k2,k3=keys[1:4]
    alpha=fixture["alpha"]
    beta=fixture["beta"]
    r,z=BitVec("r_full_ddt",32),BitVec("z_full_ddt",32)
    K1,K2,K3=[BitVecVal(k,32) for k in (k1,k2,k3)]
    A,B=[BitVecVal(w,32) for w in (alpha,beta)]
    c=G(K1,r^A)^G(K1,r)
    h=G(K2,z)
    solver=Solver()
    solver.set(timeout=timeout_ms)
    solver.add(
        (G(K2,z^c)^h)==(A^B),
        (G(K3,(r^h)^B)^G(K3,r^h))==c
    )
    models=[]
    started=time.monotonic()
    status="unknown"
    while len(models)<=model_cap:
        res=solver.check()
        if res==unsat:
            status="complete_unsat_after_enumeration"
            break
        if res!=sat:
            status="unknown"
            break
        m=solver.model()
        ri=m.eval(r).as_long()
        zi=m.eval(z).as_long()
        # Independent direct real-five-round replay.
        original_right=zi^g(k1,ri)
        original_left=ri^g(keys[0],original_right)
        original=(original_left<<32)|original_right
        second=original^(alpha<<32)
        diff=five_round(keys,original)^five_round(keys,second)
        assert diff==beta,(hex(diff),hex(beta),hex(ri),hex(zi))
        assert (g(k2,zi^ (g(k1,ri^alpha)^g(k1,ri))) ^
                g(k2,zi))==(alpha^beta)
        models.append((ri,zi))
        solver.add(Or(r!=BitVecVal(ri,32),z!=BitVecVal(zi,32)))
        if len(models)%64==0:
            print("SMT_COUNT_PROGRESS",len(models),"elapsed_s",
                  round(time.monotonic()-started,2),flush=True)
    if len(models)>model_cap:
        status="model_cap"
    if status=="complete_unsat_after_enumeration" and expected is not None:
        assert len(models)==expected,(len(models),expected)
    words="".join(f"{a:08x}{b:08x}\n" for a,b in sorted(models))
    outcome=dict(
        fixture=fixture["name"],
        input=f"0x{alpha:08x}",
        output=f"0x{beta:08x}",
        keys=[f"0x{k:08x}" for k in keys],
        status=status,
        verified_models=len(models),
        expected=expected,
        sha256_pairs=hashlib.sha256(words.encode()).hexdigest(),
        elapsed_seconds=round(time.monotonic()-started,3),
        independent_full_five_round_feistel_replay=True,
        limitation="UNKNOWN and model_cap are not complete counts"
    )
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(outcome,indent=2)+"\n")
    print("INDEPENDENT_FULL_DDT_Z3",json.dumps(outcome,sort_keys=True),flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--fixture",type=int,default=0,choices=(0,1))
    parser.add_argument("--expected",type=int)
    parser.add_argument("--timeout-ms",type=int,default=60000)
    parser.add_argument("--model-cap",type=int,default=10000)
    parser.add_argument("--output",type=Path)
    cfg=parser.parse_args()
    path=cfg.output or ROOT/f"Magma/Differential/FiveRounds/Experiments/joint_full_z3_{cfg.fixture}.json"
    exact_enumeration(CASES[cfg.fixture],cfg.expected,cfg.timeout_ms,
                      cfg.model_cap,path)


if __name__=="__main__":
    main()
