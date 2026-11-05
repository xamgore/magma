#!/usr/bin/env python3
"""Exact Walsh/cycle check for nonlinear conjugate permutations.

Full-schedule 4-bit-word Magma toy only (256 states).
For C=H^-1 L H, Koopman permutation matrices are similar;
hence the trace of every power is equal, equivalently the
number of fixed points of C^m and L^m.

A Walsh basis is a linear change of basis of these matrices,
so full operator eigenvalues also agree; but individual
ordinary-XOR Walsh/LAT coefficients in the FIXED mask basis
generally differ. A counterexample is enumerated below.
No inference about key-Hamming-weight-only differential
probabilities is justified by similarity alone.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import json
from Magma.Differential.FullCipher.Experiments.full_schedule_macro_toy import C,T,N,H,R,swap

def iterate(f,x,m):
    for _ in range(m):x=f(x)
    return x

def walsh(f,am,bm):
    s=0
    for x in range(N):
        bit=((am&x).bit_count() ^ (bm&f(x)).bit_count())&1
        s+=1 if bit==0 else -1
    return s

def test_palindromic_16_lat_all_masks():
    # 256 Walsh masks x 256 Walsh masks, exact integer
    # transform of the actual toy 16-round palindrome graph.
    E=[R(H(x)) for x in range(N)]
    lat=[[0]*N for _ in range(N)]
    for bm in range(N):
        v=[1 if ((bm&E[x]).bit_count()&1)==0 else -1
           for x in range(N)]
        size=1
        while size<N:
            for start in range(0,N,2*size):
                for i in range(size):
                    a,b=v[start+i],v[start+i+size]
                    v[start+i]=a+b
                    v[start+i+size]=a-b
            size*=2
        for am in range(N):lat[am][bm]=v[am]
    for am in range(N):
        for bm in range(N):
            assert lat[am][bm]==lat[swap(bm)][swap(am)],(am,bm)
    return dict(ordinary_xor_LAT_cells_verified=N*N,
        exact_integer_walsh_transform=True,
        palindrome_key_schedule=True)

def main():
    lat_audit=test_palindromic_16_lat_all_masks()
    traces={}
    for m in range(1,17):
        a=sum(iterate(C,x,m)==x for x in range(N))
        b=sum(iterate(T,x,m)==x for x in range(N))
        assert a==b
        traces[m]=a
    witness=None
    for a in range(1,N):
      for b in range(1,N):
        wc=walsh(C,a,b);wt=walsh(T,a,b)
        if wc!=wt:
            witness=dict(alpha_mask=hex(a),beta_mask=hex(b),
                walsh_full_C=wc,walsh_short_L=wt)
            break
      if witness:break
    assert witness
    print("NONLINEAR_CONJUGACY_SPECTRAL_AUDIT_OK",
          json.dumps(dict(
              scope="8-bit total state / one-S-box toy",
              palindrome16_lat_reflection=lat_audit,
              traces_of_permutation_powers_equal=True,
              fixed_points_of_powers=traces,
              fixed_mask_Walsh_mismatch=witness,
              valid_invariant="Koopman similarity: eigenvalues, cycle type, traces",
              invalid_invariant="Untransformed Walsh/LAT coefficients"),
              sort_keys=True),flush=True)

if __name__=="__main__":main()
