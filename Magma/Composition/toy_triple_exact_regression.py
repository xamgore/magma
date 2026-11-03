#!/usr/bin/env python3
"""Exhaustive 8-bit TWO-nibble Feistel test of exact five-round triple joins.

This is a small *toy projection* using Magma's first two RFC S-boxes,
8-bit modular addition, and rotate-left-3, not the full 32-bit Magma.
Its role is to test the exact weighted COUNTING identity (including
coarse-join overcount) on a completely enumerable state space.

Three independent computations of the same fixed-key five-round
outer DDT count:
 A) direct 2^16 two-half plaintext base states;
 B) exact triple g-derivative join over 2^8 * 2^8 (r,z);
 C) product of two 2-nibble, two-carry tagged traces, with both
    true rotation-cross-nibble dependencies checked.

D) The naive two-DDT convolution is an upper bound, often STRICT.

A successful test does NOT prove the full-width triple DP efficient,
nor certify the toy in Lean. The full-width 32-bit one-round
reconstruction and carry chaining are established in
TaggedCarryWord.lean.
"""
import argparse
import collections
import json
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
from verify_nround import BOX

MASK = 0xff


def rol3(x):
    return ((x << 3) | (x >> 5)) & MASK


def ror3(x):
    return ((x >> 3) | (x << 5)) & MASK


def nibble(x, i):
    return (x >> (4*i)) & 15


def pack(ds):
    assert len(ds)==2
    return ds[0] | ds[1]<<4


def toy_g(k, x):
    q=(k+x)&MASK
    y=BOX[0][q&15]|(BOX[1][(q>>4)&15]<<4)
    return rol3(y)


def toy_gdiff(k,x,d):
    return toy_g(k,x^d)^toy_g(k,x)


def toy_tagged_step(i,k,d,x,s):
    c0,c1=s
    b0=x+k+c0
    b1=(x^d)+k+c1
    u=BOX[i][b0&15]
    v=BOX[i][b1&15]
    return u,u^v,(b0>>4,b1>>4)


def tagged_word(k,d,x):
    s=(0,0)
    b,e=[],[]
    for i in range(2):
        u,v,s=toy_tagged_step(i,nibble(k,i),nibble(d,i),nibble(x,i),s)
        b.append(u);e.append(v)
    assert rol3(pack(b))==toy_g(k,x)
    assert rol3(pack(e))==toy_gdiff(k,x,d)
    return b,e


def mixed(tags,i):
    """Cyclic rotate-left-3: 3 high previous + 1 low current."""
    return (tags[(i-1)%2]>>1)|((tags[i]&1)<<3)


def triple_local_two_nibbles(k1,k2,k3,a,b,r,z):
    """Independent two-nibble carry evaluation of triple condition."""
    # The first tagged word determines the c difference by real
    # Magma-style local addition, not by treating c as independent.
    base1,e=tagged_word(k1,a,r)
    c=rol3(pack(e))
    base2,f=tagged_word(k2,c,z)
    h=rol3(pack(base2))
    # The local third-word input is really r XOR h.
    w=r^h
    base3,t=tagged_word(k3,b,w)
    assert all(nibble(c,i)==mixed(e,i) for i in range(2))
    assert all(nibble(h,i)==mixed(base2,i) for i in range(2))
    assert all(nibble(w,i)==(nibble(r,i)^mixed(base2,i)) for i in range(2))
    return pack(f)==ror3(a^b) and pack(t)==pack(e)


def triple_exact(k1,k2,k3,a,b):
    """Exact 16-bit state cardinality, in bijective (r,z) coordinates."""
    candidates=collections.Counter()
    accepted=0
    for r in range(256):
        c=toy_gdiff(k1,r,a)
        candidates[c]+=1
        for z in range(256):
            if toy_gdiff(k2,z,c)==(a^b):
                w=r^toy_g(k2,z)
                if toy_gdiff(k3,w,b)==c:
                    accepted+=1
    return accepted,candidates


def triple_local_count(k1,k2,k3,a,b):
    """Same 256^2 assignments evaluated as local carry-tag traces."""
    accepted=0
    for r in range(256):
        for z in range(256):
            accepted+=int(triple_local_two_nibbles(k1,k2,k3,a,b,r,z))
    return accepted


def outer5_ddt(k0,k1,k2,k3,k4,a):
    """Exhaust exact 16-bit Feistel base space, retain only output left=0."""
    hist=collections.Counter()
    keys=(k0,k1,k2,k3,k4)
    for state in range(1<<16):
        left,right=(state>>8)&MASK,state&MASK
        left2,right2=left^a,right
        for k in keys:
            left,right=right,left^toy_g(k,right)
            left2,right2=right2,left2^toy_g(k,right2)
        if (left^left2)==0:
            hist[right^right2]+=1
    return hist


def naive_two_ddt_convolution(k1,k2,a,b):
    """Wrong as an exact five-round count: it forgets the final g fiber."""
    n=0
    for c in range(256):
        first=sum(toy_gdiff(k1,r,a)==c for r in range(256))
        if first==0:continue
        second=sum(toy_gdiff(k2,z,c)==(a^b) for z in range(256))
        n+=first*second
    return n


def toy_transfer_step(i, k1, k2, k3, a, b, state, r_digit, z_digit):
    """One local weighted contraction edge for the 2-nibble toy.

    State = (six incoming carry bits, previous E high3,
             previous U high3). Current E and U low bit is computed
    in THIS nibble, so rotate-left-3 uses 3 old bits and 1 new bit.
    """
    ca=state[0:2]
    cb=state[2:4]
    cc=state[4:6]
    prev_e_high,prev_u_high=state[6],state[7]
    _,e,ca_next=toy_tagged_step(i,nibble(k1,i),nibble(a,i),r_digit,ca)
    c_i=prev_e_high|((e&1)<<3)
    u,f,cb_next=toy_tagged_step(i,nibble(k2,i),c_i,z_digit,cb)
    h_i=prev_u_high|((u&1)<<3)
    w_i=r_digit^h_i
    _,third,cc_next=toy_tagged_step(i,nibble(k3,i),nibble(b,i),w_i,cc)
    if f!=nibble(ror3(a^b),i) or third!=e:
        return None
    return (*ca_next,*cb_next,*cc_next,e>>1,u>>1)


def toy_transfer_count(k1,k2,k3,a,b):
    """EXACT weighted two-nibble DP with cyclic tag boundary closure.

    Guess high three bits of the LAST E/U tag: 8*8=64 boundary
    labels. Each nibble enumerates its 16^2 choices of r_i,z_i.
    Keep only the six carry bits and two 3-bit delayed observations.
    After the second nibble, require both delayed observations
    equal their guessed boundary labels; final carries are free
    because toy addition is modulo 2^8.

    Every r,z appears exactly once in a closed transfer path, so
    no marginal DDT multiplication is used. This is a genuine
    weighted finite-state contraction, not a full r,z enumeration.
    """
    total=0
    total_edges=0
    max_frontier=0
    nonempty_guesses=0
    for first_e_high in range(8):
        for first_u_high in range(8):
            start=(0,0,0,0,0,0,first_e_high,first_u_high)
            dist={start:1}
            for i in range(2):
                nxt=collections.Counter()
                for state,mass in dist.items():
                    for r_digit in range(16):
                        for z_digit in range(16):
                            end=toy_transfer_step(i,k1,k2,k3,a,b,state,r_digit,z_digit)
                            if end is not None:
                                nxt[end]+=mass
                                total_edges+=1
                dist=nxt
                max_frontier=max(max_frontier,len(dist))
                if not dist:
                    break
            subtotal=sum(mass for state,mass in dist.items()
                if state[6]==first_e_high and state[7]==first_u_high)
            total+=subtotal
            nonempty_guesses+=int(subtotal>0)
    return total,dict(max_frontier=max_frontier,
        visited_local_transition_edges=total_edges,
        nonempty_cyclic_boundary_guesses=nonempty_guesses,
        boundary_guesses=64,
        carry_bits=6,
        delayed_rotation_tag_bits=6,
        total_interface_bits=12)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--seed",type=int,default=8891)
    ap.add_argument("--samples",type=int,default=2)
    ap.add_argument("--output",type=Path,default=ROOT/"Magma/Composition/toy_triple_exact_regression.json")
    cfg=ap.parse_args()
    assert 1<=cfg.samples<=10
    rng=random.Random(cfg.seed)
    began=time.monotonic()
    fixtures=[]
    for i in range(cfg.samples):
        keys=tuple(rng.getrandbits(8) for _ in range(5))
        a=0 if i==0 else rng.randrange(1,256)
        hist=outer5_ddt(*keys,a)
        if i==0:
            assert hist=={0:65536}
            b=0
        else:
            # Choose a *positive* and a zero (if present) to detect
            # an incorrectly empty join, and ensure strict defects.
            assert hist, "for 8-bit toy this input produced no outer pairs"
            b=max(hist,key=hist.get)
        count=hist.get(b,0)
        exact,counts=triple_exact(keys[1],keys[2],keys[3],a,b)
        assert exact==count,(i,count,exact)
        local=triple_local_count(keys[1],keys[2],keys[3],a,b)
        assert local==count,(i,count,local)
        transfer,stats=toy_transfer_count(keys[1],keys[2],keys[3],a,b)
        assert transfer==count,(i,count,transfer,stats)
        conv=naive_two_ddt_convolution(keys[1],keys[2],a,b)
        assert conv>=count
        fixtures.append(dict(keys=[f'{x:02x}' for x in keys],
            alpha=f'0x{a:02x}',sigma=f'0x{b:02x}',
            full_Feistel_count=count,
            exact_three_fiber_count=exact,
            exact_local_tagged_three_fiber_count=local,
            exact_weighted_transfer_count=transfer,
            transfer_frontier=stats,
            naive_DDT_convolution=conv,
            coupling_defect=conv-count,
            strict_defect=conv>count))
        print('TOY_5ROUND_EXACT',json.dumps(fixtures[-1],sort_keys=True),flush=True)
    # Specifically find one pair of matching first/middle constraints
    # which the third derivative rejects; it exposes false joins.
    assert any(t['strict_defect'] for t in fixtures), "need a strict-defect example"
    report=dict(scope='8-bit, two-nibble, RFC S-box 0/1 and rol3 toy',
        clearly_not_full_width_Magma=True,seed=cfg.seed,
        fixtures=fixtures,elapsed_seconds=round(time.monotonic()-began,3),
        proof_status='exhaustive Python finite computation, no new Lean theorem')
    cfg.output.parent.mkdir(parents=True,exist_ok=True)
    cfg.output.write_text(json.dumps(report,indent=2)+'\n')
    print('TOY_FIBER_REGRESSION_OK',len(fixtures),'CASES',
          report['elapsed_seconds'],'SECONDS',flush=True)


if __name__=='__main__':
    main()
