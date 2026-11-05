#!/usr/bin/env python3
"""Compare ROBDD S-box substitution circuits, with exact five-round counts.

Existing circuit: 16 four-variable equality minterms combined by OR.
ANF circuit: Zhegalkin polynomial (Mobius transform), monomials by AND,
output by XOR. Shannon circuit: conditional BDD ITE on 4 input bits.
All are EXACT truth-functional encodings, no cryptographic
approximation. Each uses identical 2*w real base variables.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[5]))
import argparse
import json
import sys
from pathlib import Path
DIR=Path(__file__).resolve().parent
sys.path.insert(0,str(DIR))
import Magma.Differential.Reflection.Experiments.overlap_j_circuit_bdd as cir
from Magma.Differential.Composition.Experiments.BDD.two_word_bdd_probe import solve
from Magma.Differential.Windows.Experiments.SAT.verify_nround import BOX

ORIGINAL=cir.sbox_4
def anf_sbox(M,inp,table):
    coefficients=[]
    for bit in range(4):
        c=[(v>>bit)&1 for v in table]
        for j in range(4):
            for mask in range(16):
                if mask&(1<<j):c[mask]^=c[mask^(1<<j)]
        coefficients.append(c)
    terms=[1]*16
    for mask in range(1,16):
        shift=mask.bit_length()-1
        terms[mask]=M.land(inp[shift],terms[mask^(1<<shift)])
    result=[]
    for bits in coefficients:
        out=0
        for mask in range(16):
            if bits[mask]:out=M.xor(out,terms[mask])
        result.append(out)
    return result

def ite(M,v,hi,lo):
    if hi==lo:return hi
    if hi==1 and lo==0:return v
    if hi==0 and lo==1:return M.neg(v)
    if hi==1:return M.lor(v,lo)
    if lo==0:return M.land(v,hi)
    if hi==0:return M.land(M.neg(v),lo)
    if lo==1:return M.lor(M.neg(v),hi)
    return M.lor(M.land(v,hi),M.land(M.neg(v),lo))

def shannon_sbox(M,inp,table):
    result=[]
    for bit in range(4):
        def build(t,depth):
            if all(x==t[0] for x in t):return (t[0]>>bit)&1
            assert depth<4
            return ite(M,inp[depth],build(t[1::2],depth+1),
                       build(t[::2],depth+1))
        result.append(build(list(table),0))
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--max-nodes',type=int,default=1000000)
    p.add_argument('--seconds',type=int,default=10)
    args=p.parse_args()
    table={"minterms":ORIGINAL,"ANF":anf_sbox,"Shannon":shannon_sbox}
    for w,rot,a,b in [(4,1,8,4),(8,3,1,0xd7)]:
        for method,impl in table.items():
            cir.sbox_4=impl
            for base in ('input','middle'):
                result=solve(w,(1,2,3,4,5),a,b,rot,base,'interleave',
                             args.max_nodes,args.seconds)
                if result['status']=='complete':
                    assert result['count']=={4:4,8:2}[w],result
                print("SBOX_BDD_METHOD",json.dumps(dict(
                    method=method,word_bits=w,base=base,
                    **result)),flush=True)
    cir.sbox_4=ORIGINAL
if __name__=="__main__":main()
