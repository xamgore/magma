#!/usr/bin/env python3
"""Exact signed Walsh of the REAL 32-bit Magma round function g_k,
using a two-state carry automaton, without enumerating 2^32 words.

W_k(a,b) = SUM_{x in 2^32} (-1)^parity(a & x XOR b & g_k(x)).
g_k(x)=ROL11(S(x+k mod 2^32)).
Rotate the b mask backward, then apply exact signed digit-transfer
matrices along all 8 genuine S-boxes, retaining the addition carry.

This does NOT magically compute the 64-bit LAT of C32=H^-1 J H^3:
the 8-round transfer involves multiple correlated Feistel bases.
"""
import json
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX,g
MASK=(1<<32)-1
KEYS=[
    0xffeeddcc,0xbbaa9988,0x77665544,0x33221100,
    0xf0f1f2f3,0xf4f5f6f7,0xf8f9fafb,0xfcfdfeff
]

def rol(x,s):
    return ((x<<s)|(x>>(32-s)))&MASK

def ror(x,s):
    return ((x>>s)|(x<<(32-s)))&MASK

def parity(x):
    return x.bit_count()&1

def exact_walsh_g(k,a,b):
    """Exact signed Int (not approximate), O(8*2*16)."""
    pre=ror(b,11)
    dp=[1,0]  # carry before least significant digit is zero
    for i,box in enumerate(BOX):
        ai=(a>>(4*i))&15
        bi=(pre>>(4*i))&15
        ki=(k>>(4*i))&15
        nxt=[0,0]
        for c,w in enumerate(dp):
            for xi in range(16):
                z=xi+ki+c
                sign=-1 if parity((ai&xi) ^ (bi&box[z&15])) else 1
                nxt[z>>4]+=w*sign
        dp=nxt
    return sum(dp)

def exhaustive_low16_32bit_g(k,a,preb):
    """Independent computation over all 16 low input bits.
    Higher 16 x-bits have no effect on selected low-nibble
    Sbox output masks or input parity; multiply by 2^16.
    """
    assert a<65536 and preb<65536
    ans=0
    for x in range(1<<16):
        y=(x+(k&0xffff))&0xffff
        mapped=0
        for i in range(4):
            mapped|=BOX[i][(y>>(i*4))&15]<<(4*i)
        ans+=(-1 if parity((a&x) ^ (preb&mapped)) else 1)
    return ans<<16

def main():
    # Exact boundary cases of a permutation on 32-bit words.
    for k in KEYS[:3]:
        assert exact_walsh_g(k,0,0)==(1<<32)
        for m in (1,2,0x80000000,0x80000800):
            assert exact_walsh_g(k,0,m)==0
            assert exact_walsh_g(k,m,0)==0

    cross_checks=[]
    for k in KEYS[:2]:
        for a,preb in ((1,1),(2,3),(0x1451,0x0362),(0x8811,0x0073)):
            b=rol(preb,11)
            actual=exhaustive_low16_32bit_g(k,a,preb)
            dp=exact_walsh_g(k,a,b)
            assert dp==actual,(hex(k),a,b,dp,actual)
            cross_checks.append([hex(k),hex(a),hex(b),dp])

    # Find the strongest low-Sbox nontrivial Walsh modes
    # for the first RFC word; no full-round correlation claim.
    best=[]
    for a in range(1,16):
        for pre_b in range(1,16):
            b=rol(pre_b,11)
            w=exact_walsh_g(KEYS[0],a,b)
            best.append((abs(w),a,b,w,exact_walsh_g(KEYS[1],a,b)))
    best.sort(reverse=True)
    top=[dict(input_mask=hex(a),output_mask=hex(b),
              signed_count_key0=w,signed_count_key1=w2,
              normalized_key0=w/(1<<32),
              normalized_key1=w2/(1<<32))
         for _,a,b,w,w2 in best[:8]]
    opposite=next((dict(input_mask=hex(a),output_mask=hex(b),
              signed_count_key0=w,signed_count_key1=w2,
              normalized_key0=w/(1<<32),
              normalized_key1=w2/(1<<32))
       for _,a,b,w,w2 in best if w*w2<0 and abs(w)>=(1<<30)
          and abs(w2)>=(1<<30)),None)
    print("GENUINE_MAGMA_G_EXACT_SIGNED_WALSH_CARRY_DP",
          json.dumps(dict(
            scope="real 32-bit g, eight RFC Sboxes, true carry, ROL11",
            operations_per_mask="8 nibble steps × 2 carries × 16 values",
            exact_cross_check_count=len(cross_checks),
            cross_checks=cross_checks,
            top_nontrivial_low_nibble_modes=top,
            witness_opposite_sign_across_two_real_round_keys=opposite,
            not_full32_LAT=True,
            one_key_per_run=True
          ),sort_keys=True),flush=True)

if __name__=="__main__": main()
