#!/usr/bin/env python3
"""Actual 32-round Magma-schedule toy, exact half-zero differential join.

The toy has 4-bit words and RFC first S-box; genuine modular addition
and real key-use pattern H|H|H|R with final GStar. It is NOT full RFC
64-bit Magma. Tests BOTH a mathematically exact state-labelled
16/16 join and a naive projection onto zero-half midpoint differences.

The same full-32 conditional formula is separately proved for REAL
32-bit words and true native encrypt API in Lean.

An aggregate over ALL b for each a reduces to a collision statistic
of the left projected ciphertext half at fixed right input word:
    E = sum_{r,y} (# {l : C(l,r).left=y})^2
      = sum_{a,b} D_C((a,0),(0,b)).
This can be computed from one streamed codebook instead of
materializing the 2-dimensional half-zero DDT slice. The codebook
still has 2^64 states at full RFC width: no scaling claim.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
import random
import statistics
import time
from collections import Counter

from Magma.Differential.FiveRounds.Experiments.five_factor_sparse_regression import feistel_toy
WORD=4
Q=1<<WORD
TOTAL=Q*Q
KEYS=(1,2,3,4,5,6,7,8)
MASK=Q-1


def swap(x):
    return ((x&MASK)<<WORD)|(x>>WORD)

def applied(keys, p):
    l,r=feistel_toy(keys,p>>WORD,p&MASK,1,1)
    return (l<<WORD)|r

def full_cipher(keys, p):
    return swap(applied(keys*3+keys[::-1],p))

def halfzero(mu):
    return (mu>>WORD)==0 or (mu&MASK)==0

def fiber_energy(C):
    hist=[[0]*Q for _ in range(Q)]
    for r in range(Q):
        for l in range(Q):
            hist[r][C[(l<<WORD)|r]>>WORD]+=1
    return sum(v*v for h in hist for v in h),hist

def main():
    start=time.monotonic()
    keys=KEYS
    H=[applied(keys,p) for p in range(TOTAL)]
    Hi=[0]*TOTAL
    for x,y in enumerate(H):Hi[y]=x
    assert all(H[Hi[y]]==y for y in range(TOTAL))
    f16=[H[H[x]] for x in range(TOTAL)]
    f16i=[0]*TOTAL
    for x,y in enumerate(f16):f16i[y]=x
    q16=[Hi[swap(H[x])] for x in range(TOTAL)]
    C=[full_cipher(keys,x) for x in range(TOTAL)]
    assert all(C[x]==q16[f16[x]] for x in range(TOTAL))

    D=[[0]*Q for _ in range(Q)]
    J=[[0]*Q for _ in range(Q)]
    all_real_witnesses=[]
    cuttypes={8:Counter(),16:Counter(),24:Counter()}
    for a in range(1,Q):
        alpha=a<<WORD
        for x in range(TOTAL):
            beta=C[x^alpha]^C[x]
            if beta>>WORD:continue
            b=beta&MASK
            assert b!=0  # nonzero input to a permutation
            D[a][b]+=1
            u=f16[x]
            mu=f16[x^alpha]^u
            assert q16[u^mu]^q16[u]==beta
            if halfzero(mu):
                J[a][b]+=1
            all_real_witnesses.append((a,b,x,mu))
            for cut in (8,16,24):
                k=keys*3+keys[::-1]
                y=applied(k[:cut],x)
                yp=applied(k[:cut],x^alpha)
                mid=yp^y
                cuttypes[cut]['halfzero' if halfzero(mid) else 'both_nonzero']+=1

    # Compute the SAME table by enumerating the true intermediate
    # base u and its FUNCTIONAL difference. No extra mu summation.
    by_join=[[0]*Q for _ in range(Q)]
    clipped=[[0]*Q for _ in range(Q)]
    for a in range(1,Q):
        alpha=a<<WORD
        for u in range(TOTAL):
            x=f16i[u]
            mid=f16[x^alpha]^u
            beta=q16[u^mid]^q16[u]
            if beta>>WORD:continue
            b=beta&MASK
            if b==0:continue
            by_join[a][b]+=1
            if halfzero(mid):clipped[a][b]+=1
    assert by_join==D==[row.copy() for row in D]
    assert clipped==J

    nonzero=sum(v>0 for row in D for v in row)
    total=sum(map(sum,D))
    clippedtotal=sum(map(sum,clipped))
    assert total==210 and clippedtotal==16,(total,clippedtotal)
    absent=[(a,b,D[a][b]) for a in range(1,Q)
            for b in range(1,Q) if D[a][b]>0 and J[a][b]==0]
    assert absent

    # Algebraic 'all (a,0)->(0,b) including zeros' slice sum,
    # computed in a separate way via output-half collision fibers.
    energy,hist=fiber_energy(C)
    assert energy==TOTAL+total,(energy,TOTAL,total)
    assert sum(sum(h) for h in hist)==TOTAL

    # Also an exact projection by input difference a, NO b:
    # A(a)=# {(l,r): C_left(l xor a,r)=C_left(l,r)}.
    across_b=[0]*Q
    for a in range(Q):
        across_b[a]=sum(
            ((C[x^(a<<WORD)]>>WORD)==(C[x]>>WORD))
            for x in range(TOTAL))
        expected=TOTAL if a==0 else sum(D[a])
        assert across_b[a]==expected
    assert sum(across_b)==energy

    # Unrelated ideal random 8-bit permutation baseline.
    # This is a finite toy diagnostic, NOT full 64-bit evidence.
    rng=random.Random(12345)
    keyscores=[]
    idealscores=[]
    for _ in range(600):
        randkeys=tuple(rng.randrange(Q) for _ in range(8))
        kp=[full_cipher(randkeys,p) for p in range(TOTAL)]
        ek,_=fiber_energy(kp)
        keyscores.append(ek-TOTAL)
        ideal=list(range(TOTAL))
        rng.shuffle(ideal)
        ei,_=fiber_energy(ideal)
        idealscores.append(ei-TOTAL)

    summary=dict(
        scope="4-bit words / first RFC Sbox, true 32-round key schedule",
        original_state_bits=8,
        actual_RFC_full_width_proof="Magma/Differential/FullCipher/Full32SlicedJoin.lean",
        key_words=list(keys),
        exact_16_plus_16_join_all_225_nonzero_boundary_cells=True,
        nonzero_DDT_entries=nonzero,
        genuine_input_base_witnesses=total,
        midpoint_16_has_both_nonzero=cuttypes[16]['both_nonzero'],
        midpoint_16_zero_half=cuttypes[16]['halfzero'],
        excluded_by_midpoint_projection=total-clippedtotal,
        midpoint_zero_half_fraction=round(clippedtotal/total,6),
        cut_witness_types={str(c):dict(cuttypes[c]) for c in cuttypes},
        example_false_zero_due_to_slice_only=dict(
            a=absent[0][0],b=absent[0][1],true_DDT=absent[0][2],
            slice_only_DDT=0),
        exact_sum_over_all_a_b_including_zero=energy,
        contribution_from_a_b_nonzero=total,
        trivial_a0_b0_mass=TOTAL,
        aggregate_by_projected_output_fiber_squares=energy,
        aggregate_by_projected_halfword_autocorrelations=sum(across_b),
        ideal_toy_keys=600,
        observed_toy_key_mean_nontrivial_energy=round(statistics.mean(keyscores),4),
        observed_ideal_permutation_mean_nontrivial_energy=round(statistics.mean(idealscores),4),
        ideal_exact_expected_nontrivial_energy=round(TOTAL*(Q-1)/(Q+1),4),
        observed_toy_key_sd=round(statistics.pstdev(keyscores),4),
        observed_ideal_permutation_sd=round(statistics.pstdev(idealscores),4),
        no_real_full_64bit_ddt_enumerated=True,
        elapsed_seconds=round(time.monotonic()-start,3),
    )
    print('EXACT_FULL32_HALFZERO_JOIN_AND_COLLISION_ENERGY_OK',
        json.dumps(summary,sort_keys=True),flush=True)

if __name__=='__main__':main()
