#!/usr/bin/env python3
"""Exhaustive single-Sbox toy: exact RFC schedule, global conjugacy,
adapted-geometry DDT and counterexample to naive XOR simplification."""
import json,time
from five_factor_sparse_regression import feistel_toy,g_toy
W=4; N=256; keys=(1,2,3,4,5,6,7,8)
def enc(p):return (p[0]<<4)|p[1]
def dec(u):return (u>>4,u&15)
def swap(u):return ((u&15)<<4)|(u>>4)
def H(u):return enc(feistel_toy(keys,*dec(u),1,1))
def R(u):return enc(feistel_toy(keys[::-1],*dec(u),1,1))
def Hinv(u):
    l,r=dec(u)
    for key in reversed(keys):l,r=r^g_toy(key,l,1,1),l
    return enc((l,r))
def C(u):return swap(enc(feistel_toy(keys*3+keys[::-1],*dec(u),1,1)))
def Q(u):return swap(R(H(u)))
def T(u):return swap(H(H(u)))
def ddt(f,a,b):return sum((f(x^a)^f(x))==b for x in range(N))
def adapted(f,a,b):
    return sum((H(f(Hinv(H(x)^a)))^H(f(x)))==b for x in range(N))
def tau(u,d):return H(Hinv(u)^d)^u
def via_interface(a,b):
    return sum((T(u^tau(u,a))^T(u))==tau(T(u),b) for u in range(N))
def main():
    t=time.monotonic()
    for x in range(N):
        assert H(Hinv(x))==x and Hinv(H(x))==x
        assert C(x)==swap(R(H(H(H(x)))))
        assert H(C(Hinv(x)))==T(x)
        assert H(Q(Hinv(x)))==swap(x)
        assert Q(Q(x))==x
    fC=sum(C(x)==x for x in range(N))
    fT=sum(T(x)==x for x in range(N))
    fQ=sum(Q(x)==x for x in range(N))
    assert fC==fT and fQ==16
    mismatches=[]
    for a in range(1,16):
      for b in range(1,16):
        alpha=a<<4;beta=b
        assert adapted(C,alpha,beta)==ddt(T,alpha,beta)
        assert ddt(C,alpha,beta)==via_interface(alpha,beta)
        assert adapted(Q,alpha,beta)==(N if swap(alpha)==beta else 0)
        direct=ddt(Q,alpha,beta)
        linear=(N if swap(alpha)==beta else 0)
        if direct!=linear:mismatches.append((hex(alpha),hex(beta),direct,linear))
    assert mismatches
    # Every ordinary XOR-DDT coefficient of the 16-round palindrome,
    # not only selected boundary differences, satisfies the Lean
    # reflected anti-diagonal symmetry D_E(a,b)=D_E(Jb,Ja).
    etable=[R(H(u)) for u in range(N)]
    eddt=[]
    for a in range(N):
        row=[0]*N
        for x in range(N):row[etable[x^a]^etable[x]]+=1
        eddt.append(row)
    for a in range(N):
        for b in range(N):
            assert eddt[a][b]==eddt[swap(b)][swap(a)],(a,b)
    print('PALINDROMIC_E16_ALL_XOR_DDT_65536_CELLS_VERIFIED',flush=True)
    print('FULL_MACRO_4BIT_TOY_VERIFIED',json.dumps(dict(
      keys=list(keys),states=N,ddt_checks=225,
      fixed_C=fC,fixed_J_H2=fT,fixed_Q=fQ,
      ordinary_xor_counterexample=mismatches[0],
      ordinary_xor_mismatches=len(mismatches),
      elapsed_seconds=round(time.monotonic()-t,2)),sort_keys=True))
if __name__=='__main__':main()
