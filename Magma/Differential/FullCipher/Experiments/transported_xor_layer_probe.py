#!/usr/bin/env python3
"""Deterministic real RFC Magma tests of proposed low-digit quotient of tau_H.

Uses genuine 32-bit RFC 8891 S-boxes, addition, ROL11, eight fixed
32-bit master key words, actual 64-bit Feistel states. For a high-
nibble-only alpha, find u=H(x),v=H(y) with the SAME low nibble of
BOTH halves but DIFFERENT low nibble of tau_H(u,alpha). This is a
concrete failure of the proposed base-label quotient. It is NOT
a universal claim about every key, every mask or all possible quotients.

The x/y bases are independently replayed; no SAT or symbolic
unsoundness is involved. A second check at the single-g level
shows the rotation immediately destroys naive low-digit triangularity.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json,random,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]

from Magma.Differential.Windows.Experiments.SAT.verify_nround import g,rounds

KEYS=(0xffeeddcc,0xbbaa9988,0x77665544,0x33221100,
      0xf0f1f2f3,0xf4f5f6f7,0xf8f9fafb,0xfcfdfeff)
ALPHA=0x8000000000000000
MASK=0xFFFFFFFF
def H(x):
    return rounds(KEYS,x,0,8)
def pi(x,nb=4):
    mask=(1<<nb)-1
    return ((x>>32)&mask,x&mask)
def tau_of_base(x):
    return H(x^ALPHA)^H(x)
def witness(max_samples=10000):
    rng=random.Random(20261104)
    seen={}
    for n in range(max_samples):
        x=rng.getrandbits(64)
        u=H(x)
        delta=tau_of_base(x)
        label=pi(u)
        output=pi(delta)
        if label in seen:
            prev=seen[label]
            if prev["tau_low"]!=output:
                old=prev["base"]
                old_u=H(old)
                old_delta=tau_of_base(old)
                assert pi(u)==pi(old_u)
                assert pi(delta)!=pi(old_delta)
                assert H(x^ALPHA)^u==delta
                assert H(old^ALPHA)^old_u==old_delta
                return dict(
                    keys=[f"0x{k:08x}" for k in KEYS],
                    alpha=f"0x{ALPHA:016x}",
                    sample_number=n+1,
                    x=f"0x{old:016x}",y=f"0x{x:016x}",
                    u=f"0x{old_u:016x}",v=f"0x{u:016x}",
                    lower_nibble_both_halves=[hex(z) for z in label],
                    tau_u=f"0x{old_delta:016x}",
                    tau_v=f"0x{delta:016x}",
                    tau_u_lower=[hex(z) for z in pi(old_delta)],
                    tau_v_lower=[hex(z) for z in output],
                    full32_RFC=True,
                    conclusion="Same 8-bit low-nibble label, DIFFERENT 8-bit projected tau")
        else:
            seen[label]={"base":x,"tau_low":output}
    raise AssertionError("No witness within resource budget; not proof of invariant")
def all_tau_bits_not_determined(max_samples=512):
    rng=random.Random(20261104)
    seen={}
    covered=0
    collisions=0
    for n in range(1,max_samples+1):
        x=rng.getrandbits(64)
        u=H(x)
        t=H(x^ALPHA)^u
        tag=pi(u)
        for other in seen.get(tag,[]):
            assert pi(u)==tag
            covered|=t^other
            collisions+=1
        seen.setdefault(tag,[]).append(t)
        if covered == (1<<64)-1:
            return dict(samples=n,collision_pairs=collisions,
                        output_bits_refuted=covered.bit_count(),
                        source='real RFC 32-bit words; key-specific deterministic witnesses')
    raise AssertionError(f'Only {covered.bit_count()} output bits refuted')

def real_e16_reflection_witness():
    # The genuine RFC rounds 17..32 ordinary-Feistel schedule is
    # 0..7,7..0; last round here is G, not RFC's final GStar.
    x=0xf664f742b16dbb7c
    a=ALPHA
    def J(v):return ((v&0xffffffff)<<32)|(v>>32)
    def E(v):return rounds(KEYS,v,16,16)
    beta=E(x^a)^E(x)
    y=J(E(x))  # Q16(x)
    mirror_input=J(beta)
    mirror_output=E(y^mirror_input)^E(y)
    assert mirror_output==J(a)
    assert J(E(y))==x
    return dict(keys='RFC Appendix A.3',
        original_base=f'0x{x:016x}',
        original_alpha=f'0x{a:016x}',
        original_beta=f'0x{beta:016x}',
        mirrored_base=f'0x{y:016x}',
        mirrored_alpha=f'0x{mirror_input:016x}',
        mirrored_beta=f'0x{mirror_output:016x}',
        q16_involutive_at_this_base=True,
        real_RFC_32bit_g_and_key_schedule=True)

def main():
    # Both inputs have low nibble zero, but the output's low
    # nibble changes despite high-only input disturbance.
    x,y=0,0x00100000
    a,b=g(0,x),g(0,y)
    assert (x&15)==(y&15) and (a&15)!=(b&15)
    print('REAL_G_NOT_LOW_TRIANGULAR',json.dumps(dict(
        key="0x00000000",x=f"0x{x:08x}",y=f"0x{y:08x}",
        g_x=f"0x{a:08x}",g_y=f"0x{b:08x}",
        low_g_x=a&15,low_g_y=b&15),sort_keys=True),flush=True)
    print('REAL_H8_TAU_LOW_QUOTIENT_COUNTEREXAMPLE',
          json.dumps(witness(),sort_keys=True),flush=True)
    print('REAL_H8_LOW_LABEL_INSUFFICIENT_FOR_ALL_64_OUTPUT_BITS',
          json.dumps(all_tau_bits_not_determined(),sort_keys=True),flush=True)
    print('REAL_E16_ORDINARY_XOR_DDT_REFLECTED_PAIR_WITNESS',
          json.dumps(real_e16_reflection_witness(),sort_keys=True),flush=True)
if __name__=='__main__':main()
