#!/usr/bin/env python3
"""Attack-oriented gate for the RFC Magma repeated/reflected schedule.

A. ACTUAL full-width 32-bit RFC round evaluator: independently construct
16-round palindromic oracle matches using H^-1(t,t), with arbitrary
secret-key-dependent witnesses (NOT unknown-key accessible construction).

B. One-S-box 4-bit-word (8-bit total) toy:
  - all 16 palindromic matches among 256 states for each tested key
  - no analogous forced 16-match public condition for the full C32
  - compare single-key q=16 chosen-input collision test to ideal
    uniform random permutations, using independent random seeds.

C. Finite *abstract permutation* analog of the FULL macro
C=H^-1 J H^3 on N=8 points. Enumerate all 8! arbitrary H
and all 8! candidate C. Image omits many individual
permutations, but includes all SAME-PARITY cycle types.
This is exact ONLY at N=8, not a theorem for N=2^64.

No attack on the standard full-32 unknown-key oracle is claimed.
"""
from collections import Counter,defaultdict
from itertools import permutations
from math import factorial
from pathlib import Path
import json
import random
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import g,rounds
sys.path.insert(0,str(Path(__file__).resolve().parent))
from five_factor_sparse_regression import feistel_toy

MASK=(1<<32)-1
KEYS=(0xffeeddcc,0xbbaa9988,0x77665544,0x33221100,
      0xf0f1f2f3,0xf4f5f6f7,0xf8f9fafb,0xfcfdfeff)
TOY_STATES=256

def swap64(v):
    return ((v&MASK)<<32)|(v>>32)
def hinv8(u):
    l,r=(u>>32)&MASK,u&MASK
    for k in reversed(KEYS):
        l,r=r^g(k,l),l
    return (l<<32)|r

def real_full_width_witnesses():
    rng=random.Random(20261105)
    witness=None
    for i in range(24):
        t=rng.getrandbits(32)
        diagonal=(t<<32)|t
        x=hinv8(diagonal)
        assert rounds(KEYS,x,0,8)==diagonal
        y=rounds(KEYS,x,16,16)
        assert y==swap64(x)
        if witness is None:
            witness=dict(diagonal=f"0x{diagonal:016x}",
                         plaintext=f"0x{x:016x}",
                         palindromic16_ciphertext=f"0x{y:016x}",
                         swapped_plaintext=f"0x{swap64(x):016x}")
    return dict(genuine_RFC_32bit_modular_add_Sboxes_ROL11=True,
                native_palindrome_rounds=list(range(8))+list(range(7,-1,-1)),
                constructed_key_dependent_witnesses=24,
                sample=witness,
                no_unknown_key_oracle_witness_generator=True)

def toy_eval(keys,x):
    l,r=feistel_toy(keys,x>>4,x&15,1,1)
    return (l<<4)|r
def toy_swap(x):
    return ((x&15)<<4)|(x>>4)
def toy_full(keys,x):
    return toy_swap(toy_eval(keys*3+keys[::-1],x))
def toy_pal(keys,x):
    return toy_eval(keys+keys[::-1],x)

def test_chosen_oracle():
    rng=random.Random(0xD155C0DE)
    sample_keys=600
    q=16
    fixed_pal=Counter()
    fixed_full=Counter()
    swap_full=Counter()
    succ_pal=succ_full_fix=succ_full_swap=succ_ideal=0
    for _ in range(sample_keys):
        keys=tuple(rng.randrange(16) for _ in range(8))
        p=[toy_pal(keys,x) for x in range(TOY_STATES)]
        c=[toy_full(keys,x) for x in range(TOY_STATES)]
        target=[toy_swap(x) for x in range(TOY_STATES)]
        n_pal=sum(p[x]==target[x] for x in range(TOY_STATES))
        n_fix=sum(c[x]==x for x in range(TOY_STATES))
        n_swap=sum(c[x]==target[x] for x in range(TOY_STATES))
        fixed_pal[n_pal]+=1
        fixed_full[n_fix]+=1
        swap_full[n_swap]+=1
        assert n_pal==16
        queried=rng.sample(range(TOY_STATES),q)
        succ_pal+=any(p[x]==target[x] for x in queried)
        succ_full_fix+=any(c[x]==x for x in queried)
        succ_full_swap+=any(c[x]==target[x] for x in queried)
        ideal=list(range(TOY_STATES))
        rng.shuffle(ideal)
        succ_ideal+=any(ideal[x]==target[x] for x in queried)
    return dict(toy_word_bits=4,toy_total_state_bits=8,
        sampled_independent_master_keys=sample_keys,
        no_key_knowledge_needed_for_oracle_test=True,
        q_distinct_chosen_inputs=q,
        exact_palindromic16_swap_matches_per_key=dict(fixed_pal),
        mean_full32_fixed=sum(k*v for k,v in fixed_full.items())/sample_keys,
        mean_full32_swap_matches=sum(k*v for k,v in swap_full.items())/sample_keys,
        success_palindromic16=succ_pal,
        success_full32_identity=succ_full_fix,
        success_full32_swap=succ_full_swap,
        success_random_permutation_swap=succ_ideal,
        theoretical_random_permutation_probability_at_single_input=1/TOY_STATES,
        not_an_extrapolation_to_real_64bit_full32=True)

def compose(a,b):return tuple(a[i] for i in b)
def inv(a):
    r=[0]*len(a)
    for i,v in enumerate(a):r[v]=i
    return tuple(r)
def cycle_type(a):
    seen=set();sizes=[]
    for i in range(len(a)):
        if i in seen:continue
        n=0;x=i
        while x not in seen:seen.add(x);n+=1;x=a[x]
        sizes.append(n)
    return tuple(sorted(sizes))

def macro_cycle_image():
    n=8
    J=list(range(n))
    J[0],J[1]=1,0
    J[2],J[3]=3,2
    J=tuple(J) # 4 fixed points; J is EVEN
    image=set()
    for h in permutations(range(n)):
        h2=compose(h,h)
        h3=compose(h,h2)
        image.add(compose(inv(h),compose(J,h3)))
    image_classes={cycle_type(p) for p in image}
    even_classes={cycle_type(p) for p in permutations(range(n))
                  if (n-len(cycle_type(p)))%2==0}
    assert image_classes==even_classes
    assert len(image)<factorial(n)//2
    return dict(abstract_state_size=n,
        J_fixed_points=4,
        J_two_cycles=2,
        total_arbitrary_H=factorial(n),
        distinct_full_macro_permutations=len(image),
        all_even_permutations=factorial(n)//2,
        missing_individual_even_permutations=factorial(n)//2-len(image),
        all_even_cycle_types_represented=len(even_classes),
        missing_even_cycle_types=0,
        implication="No nontrivial cycle-TYPE exclusion in this small abstract model beyond parity",
        not_a_64bit_theorem=True)

def main():
    print("REAL_16ROUND_OBSERVABLE_MATCH_WITNESSES",
          json.dumps(real_full_width_witnesses(),sort_keys=True),flush=True)
    print("TOY_ORACLE_MODEL_COMPARISON",
          json.dumps(test_chosen_oracle(),sort_keys=True),flush=True)
    print("ABSTRACT_FULL_MACRO_CYCLE_IMAGE",
          json.dumps(macro_cycle_image(),sort_keys=True),flush=True)
    print("MACRO_ATTACK_GATE_OK",flush=True)

if __name__=="__main__":main()
