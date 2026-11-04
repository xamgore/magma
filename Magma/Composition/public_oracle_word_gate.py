#!/usr/bin/env python3
"""Exhaustive falsification of SIMPLE KEY-UNIVERSAL public word identities.

Alphabet F=C_K, I=C_K^{-1}, J=the public half swap.
Enumerate ALL nonempty freely reduced words of length <=12,
where FI=IF=JJ are mechanically canceled.

For EVERY candidate word W(F,I,J), one actual genuine-RFC
256-bit K and one actual 64-bit base x suffice to refute
W(x)=x if W(x)!=x. This is a *finite COMPUTATIONAL negative
certificate*, not a Lean theorem.

This does NOT rule out other observable XOR equations,
statistics, long word identities, nor attacks on full Magma.
It is a focused gate against unjustified "palindrome implies
a short PUBLIC operator identity" attacks.

The real Cfull and Cfull_inv come from the independent
RFC arithmetic evaluator in full_key_msb_gauge_verify.py.
"""
import hashlib
import json
from full_key_msb_gauge_verify import Cfull,Cfull_inv,J64,KEYS,T64

BASE=0x0123456789abcdef
MAXLEN=12

def action(op,x):
    if op=='F': return Cfull(KEYS,x)
    if op=='I': return Cfull_inv(KEYS,x)
    if op=='J': return J64(x)
    raise ValueError(op)

def canceled(last,op):
    return ((last=='F' and op=='I') or
            (last=='I' and op=='F') or
            (last=='J' and op=='J'))

def main():
    for x in [0,1,BASE,(1<<64)-1,0x8000000080000000]:
        assert Cfull_inv(KEYS,Cfull(KEYS,x))==x
        assert Cfull(KEYS,Cfull_inv(KEYS,x))==x
        assert J64(J64(x))==x

    # The known XOR state translation is a CROSS-KEY symmetry;
    # it is NOT in general a commutation law for C_K alone.
    same_key_lhs=Cfull(KEYS,BASE^T64)
    same_key_rhs=Cfull(KEYS,BASE)^T64
    assert same_key_lhs!=same_key_rhs
    print('NATIVE_SINGLE_KEY_MSB_COMMUTATION_FALSE',json.dumps(dict(
        K='RFC Appendix A.3',x=f'0x{BASE:016x}',
        left=f'0x{same_key_lhs:016x}',right=f'0x{same_key_rhs:016x}',
        no_same_key_gauge=True),sort_keys=True),flush=True)
    sha=hashlib.sha256()
    level=[('',BASE)]
    by_length={}
    all_survivors=[]
    for length in range(1,MAXLEN+1):
        nextlevel=[]
        for word,base in level:
            for op in 'FIJ':
                if word and canceled(word[-1],op):continue
                w=word+op
                y=action(op,base)
                sha.update(w.encode()+b'\t'+f'{y:016x}'.encode()+b'\n')
                if y==BASE:all_survivors.append(w)
                nextlevel.append((w,y))
        by_length[length]=len(nextlevel)
        assert by_length[length]==3*(2**(length-1))
        level=nextlevel

    assert not all_survivors,all_survivors
    print('NATIVE_32ROUND_PUBLIC_WORD_IDENTITY_GATE_OK',
          json.dumps(dict(
              keys='RFC Appendix A.3 all eight 32-bit words',
              tested_input=f'0x{BASE:016x}',
              all_nonempty_reduced_operator_words= sum(by_length.values()),
              maximum_length=MAXLEN,
              tested_lengths=by_length,
              universal_identity_candidates_surviving=0,
              trace_sha256=sha.hexdigest(),
              alphabet='F=C_K; I=C_K^-1; J=public half-swap',
              interpretation='all 12285 short NONTRIVIAL key-universal identities in this restricted language REFUTED by one real K,x',
              not_an_exclusion_of_XOR_or_statistical_or_longer_relations=True),
              sort_keys=True),flush=True)

if __name__=='__main__':main()
