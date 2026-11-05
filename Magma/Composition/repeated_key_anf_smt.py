#!/usr/bin/env python3
"""Optional research-only Boolean-ANF Sbox formulation of real Magma g.

Same known plaintext/ciphertext samples and oracle as
repeated_key_long_smt.py, but Sboxes are 4-input ANFs
rather than Store/Select arrays. This is a solver encoding
experiment, not a new cryptographic assertion.
"""
import argparse,json,random,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
import repeated_key_long_smt as base
z3=base.z3

def coeffs(row,bit):
    a=[(x>>bit)&1 for x in row]
    for i in range(4):
        for m in range(16):
            if m&(1<<i):
                a[m]^=a[m^(1<<i)]
    return [i for i in range(16) if a[i]]

ANF=[tuple(coeffs(box,b) for b in range(4)) for box in base.BOX]

def sbox_anf(index,nib):
    bits=[z3.Extract(i,i,nib) for i in range(4)]
    m=[None]*16;m[0]=z3.BitVecVal(1,1)
    for k in range(1,16):
        lowest=k&-k; b=lowest.bit_length()-1
        m[k]=m[k^lowest]&bits[b]
    outputs=[]
    for masks in ANF[index]:
        if len(masks)==0:v=z3.BitVecVal(0,1)
        else:
            v=m[masks[0]]
            for k in masks[1:]:
                v=v^m[k]
        outputs.append(v)
    return z3.Concat(*reversed(outputs))

def anf_g(k,x):
    z=k+x
    out=z3.Concat(*[
        sbox_anf(i,z3.Extract(4*i+3,4*i,z))
        for i in range(7,-1,-1)])
    return z3.RotateLeft(out,11)

def main():
    arg=argparse.ArgumentParser()
    arg.add_argument('--pattern',default='ABAB')
    arg.add_argument('--pairs',type=int,default=2)
    arg.add_argument('--timeout',type=int,default=20000)
    arg.add_argument('--seed',type=int,default=4106)
    args=arg.parse_args()
    # Exact exhaustive equivalence for each native RFC 4-bit Sbox.
    for i,box in enumerate(base.BOX):
        for x in range(16):
            got=z3.simplify(sbox_anf(i,z3.BitVecVal(x,4))).as_long()
            assert got==box[x],(i,x,got,box[x])
    # Also cross-check full-word ANF against independent native RFC g.
    rng=random.Random(77813)
    for _ in range(100):
        k,x=rng.getrandbits(32),rng.getrandbits(32)
        observed=z3.simplify(anf_g(z3.BitVecVal(k,32),z3.BitVecVal(x,32)))
        assert observed.as_long()==base.g_reference(k,x)
    base.z3_g=anf_g
    out=base.check_one(args.pattern,args.pairs,args.seed,args.timeout,
                       verbose=True)
    out['encoding']='nibble_anf'
    print('REPEATED_KEY_ANF_SMT',json.dumps(out,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
