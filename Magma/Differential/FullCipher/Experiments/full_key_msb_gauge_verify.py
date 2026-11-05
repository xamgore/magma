#!/usr/bin/env python3
"""Independent RFC32 related-key top-bit gauge regression.

A real full-width round-key transformation flips bit 31 in ALL eight
32-bit words, while T flips bit31 in BOTH 32-bit state words.
Direct 32-round RFC replay checks
    C_Kflip(T(x)) == T(C_K(x))
at thousands of deterministic bases. This is a POSITIVE
related-key identity, NOT a cryptanalytic zero claim.

The 4-bit-word one-RFC-S-box toy checks ALL 256 input bases,
ALL 65536 regular XOR-DDT coefficients and ALL 65536 Walsh/LAT
coefficients for the corresponding top-bit transformation.

No 2^64 full-width DDT is computed. Lean proves the
full-width key-universal identity independently.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import random
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import g,rounds
sys.path.insert(0,str(Path(__file__).resolve().parent))
from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy

HI32=0x80000000
T64=(HI32<<32)|HI32
KEYS=(0xffeeddcc,0xbbaa9988,0x77665544,0x33221100,
      0xf0f1f2f3,0xf4f5f6f7,0xf8f9fafb,0xfcfdfeff)

def J64(x):return ((x&0xffffffff)<<32)|(x>>32)
def Cfull(k,x):return J64(rounds(k,x,0,32))
def Cfull_inv(k,y):
    v=J64(y)
    l,r=v>>32,v&0xffffffff
    seq=k*3+k[::-1]
    for key in reversed(seq):
        l,r=r^g(key,l),l
    return (l<<32)|r

def toyC(k,x):
    l,r=x>>4,x&15
    left,right=feistel_toy(k*3+k[::-1],l,r,1,1)
    return (right<<4)|left

def toy_ddt(table):
    n=len(table)
    rows=[[0]*n for _ in range(n)]
    for a in range(n):
        row=rows[a]
        for x in range(n):
            row[table[x^a]^table[x]]+=1
    return rows

def toy_lat(table):
    n=len(table)
    ans=[[0]*n for _ in range(n)]
    for b in range(n):
        response=[1 if ((b&table[x]).bit_count()%2)==0 else -1
                  for x in range(n)]
        s=1
        while s<n:
            for i in range(0,n,2*s):
                for j in range(s):
                    u,v=response[i+j],response[i+j+s]
                    response[i+j]=u+v
                    response[i+j+s]=u-v
            s*=2
        for a in range(n):
            ans[a][b]=response[a]
    return ans

def main():
    started=time.monotonic()
    rng=random.Random(0x20261104)
    kflip=tuple(k^HI32 for k in KEYS)
    for i in range(512):
        x=rng.getrandbits(32)
        k=rng.getrandbits(32)
        assert g(k^HI32,x^HI32)==g(k,x),(i,k,x)
    for i in range(1024):
        x=rng.getrandbits(64)
        assert Cfull(kflip,x^T64)==Cfull(KEYS,x)^T64,(i,x)
    for i in range(256):
        y=rng.getrandbits(64)
        assert Cfull(KEYS,Cfull_inv(KEYS,y))==y
        assert Cfull_inv(kflip,y^T64)==Cfull_inv(KEYS,y)^T64
    print("REAL_RFC32_KEY_MSB_GAUGE_POINTWISE_VERIFIED",
        json.dumps(dict(all_32_bit_key_words_flipped=True,
          actual_RFC_keys=[f"0x{k:08x}" for k in KEYS],
          input_state_mask=f"0x{T64:016x}",
          tested_round_function_bases=512,
          tested_32_round_plaintexts=1024,
          tested_32_round_inverse_outputs=256,
          true_RFC32_modular_add_Sbox_ROL11_GStar=True,
          seconds=round(time.monotonic()-started,3)),
        sort_keys=True),flush=True)

    keys=(1,2,3,4,5,6,7,8)
    hi4=8
    tt=(hi4<<4)|hi4
    kf=tuple(k^hi4 for k in keys)
    orig=[toyC(keys,x) for x in range(256)]
    flip=[toyC(kf,x) for x in range(256)]
    assert all(flip[x^tt]==orig[x]^tt for x in range(256))
    tab1,tab2=toy_ddt(orig),toy_ddt(flip)
    assert tab1==tab2
    lat1,lat2=toy_lat(orig),toy_lat(flip)
    for a in range(256):
        for b in range(256):
            parity=((a&tt).bit_count()+(b&tt).bit_count())&1
            assert lat2[a][b]==(-lat1[a][b] if parity else lat1[a][b]),(a,b)
    inverse_orig=[0]*256
    inverse_flip=[0]*256
    for x in range(256):
        inverse_orig[orig[x]]=x
        inverse_flip[flip[x]]=x
    assert all(orig[inverse_orig[y]]==y and flip[inverse_flip[y]]==y
               for y in range(256))
    bct_equal=0
    bct_positive=0
    for a in range(256):
        for b in range(256):
            count1=sum(
                (inverse_orig[orig[x]^b] ^
                    inverse_orig[orig[x^a]^b])==a
                for x in range(256))
            count2=sum(
                (inverse_flip[flip[x]^b] ^
                    inverse_flip[flip[x^a]^b])==a
                for x in range(256))
            assert count1==count2,(a,b,count1,count2)
            bct_equal+=1
            bct_positive+=(count1>0)
    assert bct_equal==65536
    nonzero=sum(v!=0 for row in tab1 for v in row)
    print("ALL_TOY_FULL32_KEY_MSB_DDT_LAT_BCT_VERIFIED",
      json.dumps(dict(tested_key_words=list(keys),flipped_key_words=list(kf),
         toy_RFC_Sbox0=True,DDT_cells_compared=65536,
         LAT_cells_compared=65536,BCT_cells_compared=bct_equal,
         positive_BCT_cells=bct_positive,
         nonzero_DDT_cells=nonzero,exact_Lat_sign_rule=True,
         full_width_result='only sampled RFC 32bit points; Lean proves universal',
         seconds=round(time.monotonic()-started,3)),sort_keys=True),flush=True)

if __name__=="__main__":main()
