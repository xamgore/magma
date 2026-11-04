#!/usr/bin/env python3
"""Candidate all-keys seven-round impossible-differential theorem.

For any fixed RFC Magma g key, XOR-input difference in highest
nibble H=0xf0000000 forces output difference within R=0x780.
Conversely, output difference within R implies input within H.
Finally, a nonzero input difference supported in R cannot produce
an output difference supported in H. These are UNIVERSAL
one-round statements (for ALL 32-bit k,x,d), not a fixed-key
sampling experiment.

If all local lemmas hold, the genuine five-round inner difference
stream (0,a,p,q,t,b,0) with nonzero a,b in H is contradictory:
p,t in R, and p!=0 (g is a permutation).
Delta g2(q) = p XOR t in R -> q in H.
Delta g1(p) = a XOR q in H, impossible for p in R nonzero.

Therefore the seven-round outer DDT (a,0)->(0,b) is ZERO
for ALL independent round keys, and consequently ALL admissible
Magma master keys, for ALL 15*15=225 nonzero highest-nibble
boundary values. This result needs local universal UNSAT
certificates or a kernel proof; UNKNOWN is not evidence.

This script attempts independent Z3 bit-vector UNSAT checks for
the necessary one-round universal assertions, and reports
statuses separately. It is not a slow 7-round SAT matrix.
"""
import json
import sys
import time
from pathlib import Path

DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
from opposite_five_fiber import z3_g_library
from z3 import BitVec,BitVecVal,Solver,sat,unsat

H=0xf0000000
R=0x00000780
MASK=0xffffffff

def check(name,term,extra,ms=15000):
    k,x,d=term
    G=z3_g_library()
    gdelta=G(k,x^d)^G(k,x)
    s=Solver()
    s.set(timeout=ms)
    s.add(extra(k,x,d,gdelta))
    begin=time.monotonic()
    result=s.check()
    dct=dict(lemma=name,
            status="UNSAT" if result==unsat else
                   "SAT" if result==sat else "UNKNOWN",
            seconds=round(time.monotonic()-begin,3))
    if result==sat:
        m=s.model()
        dct["counterexample"]={v:hex(m.eval(e).as_long()) for v,e in
                               [('key',k),('base',x),('difference',d),
                                ('delta_g',gdelta)]}
    if result!=unsat:
        print("UNIVERSAL_G_LEMMA_NOT_CERTIFIED",json.dumps(dct),flush=True)
    else:
        print("UNIVERSAL_G_LEMMA_UNSAT",json.dumps(dct),flush=True)
    return dct

def main():
    k,x,d=[BitVec(v,32) for v in ('global_k','global_x','global_d')]
    bv=lambda v:BitVecVal(v,32)
    allbits=bv(MASK)
    cases=[
      ("high_input_implies_low_output",
       lambda k,x,d,e:(d & bv(MASK^H)==bv(0)) &
                        (e & bv(MASK^R)!=bv(0))),
      ("low_output_implies_high_input",
       lambda k,x,d,e:(e & bv(MASK^R)==bv(0)) &
                        (d & bv(MASK^H)!=bv(0))),
      ("nonzero_low_input_cannot_have_high_output",
       lambda k,x,d,e:(d!=bv(0)) &
                        (d & bv(MASK^R)==bv(0)) &
                        (e & bv(MASK^H)==bv(0))),
      ("g_bijective_no_nonzero_zero_derivative",
       lambda k,x,d,e:(d!=bv(0)) & (e==bv(0))),
    ]
    reports=[check(name,(k,x,d),condition) for name,condition in cases]
    if all(p["status"]=="UNSAT" for p in reports):
        print("UNIVERSAL_SEVEN_TOP_NIBBLE_THEOREM_LOCAL_GATE_OK",
              json.dumps(dict(outer_rounds=7,
                  nonzero_high_nibble_endpoints=225,
                  all_keys=True,local_lemmas=reports),sort_keys=True),
              flush=True)
    else:
        print("UNIVERSAL_SEVEN_TOP_NIBBLE_THEOREM_NOT_ESTABLISHED",
              json.dumps(reports,sort_keys=True),flush=True)

if __name__=="__main__":main()
