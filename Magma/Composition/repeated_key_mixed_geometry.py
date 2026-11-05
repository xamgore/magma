#!/usr/bin/env python3
"""Exact mixed XOR/modular constraint recovery for genuine RFC 8891 g rounds.

Models REAL 32-bit modular addition, all EIGHT RFC S-boxes,
11-bit rotation and true Feistel G; 2x G_k and 3x G_a,G_b,G_a.
It is a reduced-round result; never extrapolate to full 32 rounds.

For 3 rounds, output (Q,U) for plaintext (L,R) satisfies
    g_a(R) XOR g_a(Q) = L XOR U
with intermediate P=L XOR g_a(R). After finding a:
    b = S^-1(ROR11(Q XOR R)) - P (mod 2^32).

The repeated-key constraint on a is solved exactly digit-wise
by TWO simultaneous 32-bit additions R+a,Q+a. For each 4-bit
digit, keep two genuine carries. Test the genuine Sbox's
XOR-output differential. With several known pairs, the SAME
key nibbles must satisfy every pair's constraints.
No difference-marginal multiplication or independence assumption.
"""
from __future__ import annotations
import json
import random
import sys
import time
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"research"))
from verify_nround import BOX, g as g_reference

MASK=(1<<32)-1
INVBOX=tuple(tuple(next(i for i in range(16) if row[i]==v)
                   for v in range(16)) for row in BOX)
assert all(sorted(row)==list(range(16)) for row in BOX)

def rol11(x):
    return ((x<<11)|(x>>21))&MASK

def ror11(x):
    return ((x>>11)|(x<<21))&MASK

def sbox(x):
    return sum(BOX[i][(x>>(4*i))&15]<<(4*i) for i in range(8))

def inverse_sbox(x):
    return sum(INVBOX[i][(x>>(4*i))&15]<<(4*i) for i in range(8))

def g(k,x):
    return rol11(sbox((x+k)&MASK))

def infer_key_for_g_value(x,g_value):
    """Exact unique key for observed g_k(x) = g_value."""
    return (inverse_sbox(ror11(g_value))-x)&MASK

def ordinary_feistel(keys,L,R):
    for k in keys:
        L,R=R,L^g(k,R)
    return L,R

def recon2_one_pair(L,R,U,V):
    """First half of G_k o G_k leaks k, second half verifies."""
    k=infer_key_for_g_value(R,U^L)
    valid=(ordinary_feistel((k,k),L,R)==(U,V))
    return [k] if valid else []

def recon2_distinct_one_pair(L,R,U,V):
    """Even DIFFERENT keys a,b can be directly recovered in TWO rounds.
    This trivial case is NOT evidence of a useful repeated-key shortcut.
    """
    a=infer_key_for_g_value(R,U^L)
    b=infer_key_for_g_value(U,V^R)
    return (a,b) if ordinary_feistel((a,b),L,R)==(U,V) else None

def make_three_constraint(L,R,Q,U):
    # From G_a,G_b,G_a: U = L XOR g_a(R) XOR g_a(Q).
    return (R,Q,ror11(L^U))

def solve_reused_a(observations, max_candidates=100000):
    """Exact 4-bit digit DP/DFS on same a in G_a,G_b,G_a.

    Each condition is (R_j,Q_j,t_j) meaning
      S(R_j+a) XOR S(Q_j+a) = t_j.
    The two additions share each key nibble, but maintain
    SEPARATE carries for the two base words.
    """
    conds=[make_three_constraint(*p) for p in observations]
    m=len(conds)
    stats=dict(nibble_trials=0,surviving_partial_assignments=0,
               candidate_keys=0, max_frontier=1)
    survivors=[]
    start_carries=(0,)*(2*m)

    def explore(i,a,carries):
        if i==8:
            stats["candidate_keys"]+=1
            if stats["candidate_keys"]>max_candidates:
                raise RuntimeError("Candidate guard hit: poorly informative observations")
            survivors.append(a)
            return
        valid=[]
        for v in range(16):
            stats["nibble_trials"]+=1
            new_carries=[]
            for j,(R,Q,target) in enumerate(conds):
                u=((R>>(4*i))&15)+v+carries[2*j]
                w=((Q>>(4*i))&15)+v+carries[2*j+1]
                if BOX[i][u&15]^BOX[i][w&15] != (target>>(4*i))&15:
                    break
                new_carries.extend((u>>4,w>>4))
            else:
                valid.append((v,tuple(new_carries)))
        stats["max_frontier"]=max(stats["max_frontier"],len(valid))
        for v,c in valid:
            stats["surviving_partial_assignments"]+=1
            explore(i+1,a|(v<<(4*i)),c)
    explore(0,0,start_carries)
    return survivors,stats

def recover3(observations):
    """Exact candidate K1,K2 pair enumeration and full ciphertext check."""
    keysA,stats=solve_reused_a(observations)
    L,R,Q,U=observations[0]
    pairs=[]
    for a in keysA:
        P=L^g(a,R)
        b=infer_key_for_g_value(P,Q^R)
        if all(ordinary_feistel((a,b,a),l,r)==(q,u)
               for l,r,q,u in observations):
            pairs.append((a,b))
    stats["full_key_candidates"]=len(pairs)
    return pairs,stats

def four_round_oracle_exact_parameterization(L,R,U,V,q):
    """For hypothesized unobserved Q after TWO rounds of a,b,a,b:
    derive k_b from final output and Q, then P, then k_a;
    finally test remaining repeated-key constraint.

    This is a 2^32-Q search in the worst case, NOT a
    practically demonstrated fast 4-round key recovery.
    """
    b=infer_key_for_g_value(U,V^q)
    P=(inverse_sbox(ror11(q^R))-b)&MASK
    a=infer_key_for_g_value(R,P^L)
    return (a,b), (g(a,q)==(U^P))

def verify():
    # Independently match native Lean RFC8891.lean g examples.
    assert g(0x87654321,0xfedcba98)==0xfdcbc20c
    assert g(0xfdcbc20c,0x87654321)==0x7e791a4b
    assert g(0x7e791a4b,0xfdcbc20c)==0xc76549ec
    assert g(0xc76549ec,0x7e791a4b)==0x9791c849
    rng=random.Random(0x465DEEDD)
    start=time.monotonic()
    n=250
    trials=[]
    one_pair_limit_hits=0
    for trial in range(n):
        a=rng.getrandbits(32)
        b=rng.getrandbits(32)
        L=rng.getrandbits(32)
        R=rng.getrandbits(32)
        Q,U=ordinary_feistel((a,b,a),L,R)
        try:
            one,s1=recover3(((L,R,Q,U),))
            assert (a,b) in one,(a,b,one)
        except RuntimeError as ex:
            assert 'Candidate guard hit' in str(ex)
            one=None
            s1=None
            one_pair_limit_hits+=1
        L2=rng.getrandbits(32)
        R2=rng.getrandbits(32)
        Q2,U2=ordinary_feistel((a,b,a),L2,R2)
        two,s2=recover3(((L,R,Q,U),(L2,R2,Q2,U2)))
        assert (a,b) in two,(a,b,two)
        if one is not None:
            assert set(two).issubset(set(one))
        assert all(ordinary_feistel((x,y,x),L2,R2)==(Q2,U2)
                   for x,y in two)
        L3=rng.getrandbits(32)
        R3=rng.getrandbits(32)
        Q3,U3=ordinary_feistel((a,b,a),L3,R3)
        three,s3=recover3(((L,R,Q,U),(L2,R2,Q2,U2),(L3,R3,Q3,U3)))
        assert (a,b) in three
        assert set(three).issubset(set(two))
        testkey=rng.getrandbits(32)
        P2,Q2full=ordinary_feistel((testkey,testkey),L,R)
        assert recon2_one_pair(L,R,P2,Q2full)==[testkey]
        otherkey=rng.getrandbits(32)
        out2=ordinary_feistel((testkey,otherkey),L,R)
        assert recon2_distinct_one_pair(L,R,*out2)==(testkey,otherkey)
        if trial<20:
            a4=rng.getrandbits(32);b4=rng.getrandbits(32)
            p=L^g(a4,R)
            hiddenq=R^g(b4,p)
            outu=p^g(a4,hiddenq)
            outv=hiddenq^g(b4,outu)
            got,valid=four_round_oracle_exact_parameterization(
                L,R,outu,outv,hiddenq)
            assert got==(a4,b4) and valid
            assert ordinary_feistel((a4,b4,a4,b4),L,R)==(outu,outv)
            if trial==0:
                # Concrete 32-bit full-round witness, not a toy.
                example=dict(
                    input=[hex(L),hex(R)],keys=[hex(a4),hex(b4)],
                    output=[hex(outu),hex(outv)],hidden_midQ=hex(hiddenq))
        trials.append((s1,s2,s3,None if one is None else len(one),
                       len(two),len(three)))
        for i in range(8):
            x=rng.getrandbits(32);k=rng.getrandbits(32)
            assert g(k,x)==g_reference(k,x)
            assert infer_key_for_g_value(x,g(k,x))==k
    one_n=Counter(t[3] for t in trials if t[3] is not None)
    two_n=Counter(t[4] for t in trials)
    three_n=Counter(t[5] for t in trials)
    report=dict(
        sample_count=n,word_bits=32,sboxes=8,rotation=11,
        actual_rfc_g_and_nibble_carries=True,
        max_input_output_samples_per_trial=3,
        schedule_2="a,a",schedule_3="a,b,a",schedule_4="a,b,a,b",
        two_round_one_pair_key_recovery_verified=n,
        two_round_distinct_keys_one_pair_recovery_verified=n,
        three_round_one_pair_candidate_counts=dict(sorted(one_n.items())),
        one_pair_capped_cases=one_pair_limit_hits,
        three_round_two_pair_candidate_counts=dict(sorted(two_n.items())),
        three_round_three_pair_candidate_counts=dict(sorted(three_n.items())),
        three_round_nibble_trials={str(j+1):
          {"mean":sum(t[j]["nibble_trials"] for t in trials if t[j] is not None)/sum(t[j] is not None for t in trials),
           "max":max(t[j]["nibble_trials"] for t in trials if t[j] is not None)}
          for j in range(3)},
        three_round_two_pair_max_candidates=max(t[4] for t in trials),
        three_round_three_pair_max_candidates=max(t[5] for t in trials),
        four_round_hidden_Q_parameterization_verified=20,
        four_round_hidden_Q_bruteforce_required_up_to=1<<32,
        four_round_example=example,
        relation_genuine_but_full32_attack_not_claimed=True,
        elapsed_seconds=round(time.monotonic()-start,3))
    print("REPEATED_KEY_GENUINE_32BIT_ROUNDS_OK",
          json.dumps(report,sort_keys=True),flush=True)

if __name__=="__main__":
    verify()
