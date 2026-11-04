#!/usr/bin/env python3
"""Exact key-independent valuation abstraction, all nibble pairs.

For every genuine g derivative, let rotR11(e) be its output
difference before rotation. The LOWEST nonzero nibble index
matches the lowest nonzero input difference nibble index.
This is a universal necessary condition under arbitrary
32-bit keys and base states because:
  (1) addition by k preserves the first differing bit;
  (2) every genuine RFC 4-bit S-box is a permutation;
  (3) rotation is explicitly undone.

For each possible lowest input nibble i and target nibble j,
ask Z3 whether ANY abstract FIVE-round difference stream
(0,a,p,q,t,b,0) is possible with arbitrary a,b having
first active nibble at i,j (higher nibbles FREE). A completed
UNSAT proves the entire family of seven-round outer
(a,0)->(0,b) DDTs zero for ALL keys, subject only to the
locally justified necessary abstraction. A SAT is NOT
a real Magma witness.

The --check-real-g option independently proves (by SMT
UNSAT queries) the eight local universal single-g
valuation properties against real RFC Magma g for fully
symbolic k,x,d. This is computational proof evidence,
not a pure Lean kernel certificate.

All cases are bounded and return UNKNOWN if timed out.
"""
import argparse
import json
import time

from z3 import BitVec,BitVecVal,RotateRight,Solver,sat,unsat
from nibble_valuation_relaxation import relation,low_nibble_pred
from opposite_five_fiber import z3_g_library

def check_g(timeout_ms=15000):
    G=z3_g_library()
    key,x,d=[BitVec(name,32) for name in ('universal_key','universal_x','universal_d')]
    rot=RotateRight(G(key,x^d)^G(key,x),11)
    out=[]
    for i in range(8):
        s=Solver()
        s.set(timeout=timeout_ms)
        s.add(low_nibble_pred(d,i))
        s.add(~low_nibble_pred(rot,i))
        started=time.monotonic()
        verdict=s.check()
        row=dict(nibble=i,status=str(verdict),
                 seconds=round(time.monotonic()-started,3))
        if verdict==sat:
            m=s.model()
            row['counterexample']={
                name:hex(m.eval(v).as_long()) for name,v in
                [('key',key),('x',x),('d',d)]}
        out.append(row)
        print("MAGMA_G_VALUATION_SOUNDNESS",json.dumps(row,sort_keys=True),flush=True)
    assert all(r['status']=='unsat' for r in out),out
    print("MAGMA_G_VALUATION_EIGHT_LOCAL_UNSAT_OK",flush=True)
    return out

def scan(rounds=5,timeout_ms=15000):
    a,b=BitVec('var_a',32),BitVec('var_b',32)
    d=[BitVecVal(0,32),a]
    d += [BitVec('var_d'+str(t),32) for t in range(2,rounds)]
    d += [b,BitVecVal(0,32)]
    assert len(d)==rounds+2
    s=Solver()
    s.set(timeout=timeout_ms)
    for i in range(rounds):
        s.add(relation(d[i+1],d[i]^d[i+2]))
    classes=[]
    table=[]
    unexpected=[]
    for i in range(8):
        line=""
        for j in range(8):
            s.push()
            s.add(low_nibble_pred(a,i),low_nibble_pred(b,j))
            t0=time.monotonic()
            status=str(s.check())
            duration=round(time.monotonic()-t0,3)
            record=dict(first_input_nibble=i,first_output_nibble=j,
                        status=status,seconds=duration)
            if status=='unsat':
                line+="X"
                n_a=15*16**(7-i)
                n_b=15*16**(7-j)
                record['nontrivial_endpoint_pairs']=n_a*n_b
                classes.append(record)
            elif status=='sat':
                line+="."
            else:
                line+="?"
                unexpected.append(record)
            s.pop()
        table.append(line)
    assert not unexpected, unexpected
    total=sum(item['nontrivial_endpoint_pairs'] for item in classes)
    result=dict(scope="genuine 32-bit Magma necessary valuation model",
        core_rounds=rounds,outer_rounds=rounds+2,
        nibble_rows=table,
        universally_rejected_minimum_nibble_classes=classes,
        total_rejected_distinct_endpoint_pairs=total,
        complete_statuses=True,
        caveat="UNSAT implies real all-key zero; SAT is not a real Magma witness")
    print("ALL_KEY_NIBBLE_VALUATION_FAMILIES",json.dumps(result,sort_keys=True),flush=True)
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--timeout-ms',type=int,default=15000)
    p.add_argument('--check-real-g',action='store_true')
    args=p.parse_args()
    if args.check_real_g:check_g(args.timeout_ms)
    r=scan(5,args.timeout_ms)
    assert r["total_rejected_distinct_endpoint_pairs"]==1908225,r
    assert len(r["universally_rejected_minimum_nibble_classes"])==6,r
    print("UNIVERSAL_SEVEN_NIBBLE_POSITION_GATE_OK",flush=True)

if __name__=='__main__':
    main()
