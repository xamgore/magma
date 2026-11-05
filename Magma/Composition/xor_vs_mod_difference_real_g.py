#!/usr/bin/env python3
"""REAL RFC 8891 g: compare XOR vs ADD differential coordinate systems.

Two different input pair transformations, always SAME underlying
native 32-bit modular-add/Sbox/ROL11 round function:
  XOR input 1: x' = x XOR 1
  MOD input 1: x' = x + 1 mod 2^32
Both outputs are measured by XOR. The event outside ROL11(low nibble)
is exact, key dependent in XOR case, key invariant in MOD case.

This does NOT recover the full Magma key: g's output is not public
after 32 rounds. The experiment measures differential key filtering
of the actual RFC round-function kernel, not SAT encoding speed.
"""
from __future__ import annotations
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import g as native_g,BOX

MASK32=(1<<32)-1
MASK=((15<<11)&MASK32)
assert MASK==0x00007800
assert all(sorted(s)==list(range(16)) for s in BOX)

def delta_xor(k,x):return native_g(k,x)^native_g(k,x^1)
def delta_add(k,x):return native_g(k,x)^native_g(k,(x+1)&MASK32)

def get_statistics(k,count=65536):
    # Exhaust low 16 input bits exactly, fixing high bits.
    high=0xa61b0000
    xor_out=add_out=0
    xor_unequal=add_unequal=0
    start=time.monotonic()
    for low in range(count):
        x=high|low
        dx=delta_xor(k,x)
        da=delta_add(k,x)
        xor_out+=int((dx & ~MASK)!=0)
        add_out+=int((da&~MASK)!=0)
        xor_unequal+=int(dx!=da)
    return dict(k=hex(k),parity=k&1,input_count=count,
                xor_input_extra_nibble=xor_out,
                add_input_extra_nibble=add_out,
                xor_input_extra_fraction=xor_out/count,
                add_input_extra_fraction=add_out/count,
                xor_vs_add_output_diff_not_equal=xor_unequal,
                seconds=round(time.monotonic()-start,3))

def differential_key_shift_algebra(k,d,x):
    # Pointwise equality underlying the exact *full*
    # modular-input / XOR-output DDT key invariance.
    # g_k(x+d) XOR g_k(x) =
    # g_0((x+k)+d) XOR g_0(x+k).
    y=(x+k)&MASK32
    return (native_g(k,(x+d)&MASK32)^native_g(k,x),
            native_g(0,(y+d)&MASK32)^native_g(0,y))

def example_mod_output_feistel_base_dependence():
    # XOR output differential of one G round is independent
    # of the LEFT base L; MOD output differential generally isn't.
    k=0x87654321
    for R in range(48):
        y=native_g(k,R)
        yp=native_g(k,R^1)
        for L in (0,0xAAAAAAAA,0x01010101,0xffffffff):
            d0=(yp-y)&MASK32
            dL=((yp^L)-(y^L))&MASK32
            if d0!=dL:
                return dict(k=hex(k),R=hex(R),left_bases=[hex(0),hex(L)],
                            xor_output_diff=hex(yp^y),
                            modulo_output_differences=[hex(d0),hex(dL)])
    raise AssertionError("No differing base found")

def main():
    start=time.monotonic()
    ks=[0,1,0x87654320,0x87654321,0xffffffff,0xfffffffe]
    stats=[get_statistics(k) for k in ks]
    for s in stats:
        k=int(s["k"],16)
        assert s['xor_input_extra_nibble']==(8192 if k&1 else 0),s
        assert s['add_input_extra_nibble']==4096,s
    # Pointwise modular translation identity on FULL native words,
    # not a reduced-width Sbox. Large deterministic selection of
    # genuinely different bases, keys and modular differences.
    checks=0
    for k in ks:
        for d in (1,2,3,0x12345678,0x80000000,0xffffffff):
            for x in (0,1,0xffffffff,0xdeadbeef,0x87654321,0x7fffffff,
                      0xabcdef01,0x10001000,0x00ff00ff):
                l,r=differential_key_shift_algebra(k,d,x)
                assert l==r,(k,x,d,l,r)
                checks+=1
    # Difference-space converter is real: input pair x,x xor 1
    # has MOD difference either +1 or -1 depending on x parity.
    pairs=[]
    for x in (0,1,2,3):
        pairs.append(dict(x=x,x_xor1=x^1,
                          modular_difference=((x^1)-x)&MASK32))
    d=dict(
        scope="true RFC g 32-bit, 8 Sboxes, 11-bit rotation",
        sample_method="exhaustive 65536 contiguous base words per key",
        output_delta="XOR, unchanged in both experiments",
        xor_pairing="x' = x XOR 1",
        modular_pairing="x' = x + 1 mod 2^32",
        extra_mask=hex(MASK),extra_means="output XOR bits outside rotated lowest Sbox nibble",
        key_shift_identity_checked=checks,
        key_shift_identity="g_k(x+d)^g_k(x)=g_0((x+k)+d)^g_0(x+k)",
        exact_full_codebook_mod_input_key_invariant=True,
        exact_parity_event_theory={
          "xor_input_even_key":"0/1",
          "xor_input_odd_key":"1/8",
          "mod_input_any_key":"1/16"
        },
        sample_statistics=stats,
        same_pair_xor_vs_add_input_label=pairs,
        mod_output_left_base_dependency=example_mod_output_feistel_base_dependence(),
        elapsed_seconds=round(time.monotonic()-start,3)
    )
    print("GENUINE_MAGMA_COMPARE_DIFFERENCE_FUNCTIONS_OK",
          json.dumps(d,sort_keys=True),flush=True)

if __name__=='__main__':
    main()
