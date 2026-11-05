#!/usr/bin/env python3
"""Bounded Z3 test on *real* 32-bit RFC Magma g with repeated 2-word schedule.

Only ordinary Feistel G rounds (last GStar would publicly swap halves).
This is a REDUCED-KEY family with at most 64 unknown key bits, never
the full 256-bit native RFC 8891 key schedule.

Two independent known plaintext/ciphertext pairs under ONE fixed key.
No ideal-cipher baseline is used: the actual keys are recovered and
independently replayed. SAT=some candidate; UNKNOWN=timeout, not UNSAT.
"""
import json
import random
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX, g as native_g

try:
    import z3
except ImportError as exc:
    raise SystemExit("Z3 Python binding required; no SAT claim") from exc

def oracle_rounds(keys, L, R):
    for key in keys:
        L,R=R,L^native_g(key,R)
    return L,R

BV4=z3.BitVecSort(4)
LOOKUPS=[]
for box in BOX:
    arr=z3.K(BV4,z3.BitVecVal(0,4))
    for x,y in enumerate(box):
        arr=z3.Store(arr,z3.BitVecVal(x,4),z3.BitVecVal(y,4))
    LOOKUPS.append(arr)

def symbolic_g(key, x):
    w=key+x
    substituted=z3.Concat(*[
        z3.Select(LOOKUPS[i],z3.Extract(4*i+3,4*i,w))
        for i in reversed(range(8))])
    return z3.RotateLeft(substituted,11)

def symbolic_rounds(n, a, b, L, R):
    for i in range(n):
        L,R=R,L^symbolic_g(a if i%2==0 else b,R)
    return L,R

def probe(rounds, timeout_ms, rng):
    true_a,true_b=rng.getrandbits(32),rng.getrandbits(32)
    schedule=tuple(true_a if i%2==0 else true_b for i in range(rounds))
    observations=[]
    for _ in range(2):
        L,R=rng.getrandbits(32),rng.getrandbits(32)
        U,V=oracle_rounds(schedule,L,R)
        observations.append((L,R,U,V))

    a,b=z3.BitVec("repeatedA",32),z3.BitVec("repeatedB",32)
    solver=z3.Solver()
    solver.set(timeout=timeout_ms)
    for L,R,U,V in observations:
        outL,outR=symbolic_rounds(
            rounds,a,b,z3.BitVecVal(L,32),z3.BitVecVal(R,32))
        solver.add(outL==z3.BitVecVal(U,32),
                   outR==z3.BitVecVal(V,32))
    t=time.monotonic()
    status=solver.check()
    result=dict(rounds=rounds,number_of_known_pairs=2,
                result=str(status),timeout_ms=timeout_ms,
                seconds=round(time.monotonic()-t,3))
    if status==z3.sat:
        recovered=(solver.model().eval(a).as_long(),
                   solver.model().eval(b).as_long())
        schedule_candidate=tuple(
            recovered[i%2] for i in range(rounds))
        result.update(
            candidate_is_true_key=recovered==(true_a,true_b),
            candidate_passes_independent_replay=all(
                oracle_rounds(schedule_candidate,L,R)==(U,V)
                for L,R,U,V in observations))
        assert result["candidate_passes_independent_replay"]
    elif status==z3.unsat:
        raise AssertionError("Real generated key must satisfy the constraints!")
    return result

def main():
    rng=random.Random(40324)
    for rounds,limit in ((4,5000),(5,6500),(6,6500),(7,6500)):
        result=probe(rounds,limit,rng)
        print("RFC_REAL_G_REPEATED_KEY_BOUNDED_SMT",
              json.dumps(result,sort_keys=True),flush=True)

if __name__=="__main__":
    main()
