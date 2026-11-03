#!/usr/bin/env python3
"""Bit-tag frontier planner for the exact opposite five-g Magma factor network.

Every emitted S-box tag bit is a separate variable, rather than a whole nibble.
This matters because rot11 is only a 1-bit/3-bit splice. The graph includes:
 - all five local dual-carry additions and derivative S-box tags;
 - all three real base-word equations;
 - all five derivative relations through p,q,t.
For alpha=0x80000000 and k0=0, the first g derivative is a single
active top-nibble S-box, so that *proved special-case simplification* is
enabled. Estimates are structural upper bounds for dense tables, NOT proof
of an exponential-time lower bound or measured runtime.
"""
import argparse
import json

from five_factor_width import eliminate


def bit_network(alpha=0x80000000, beta=0x681e60a7, k0=0):
    w = {}
    f = []
    simple = (alpha == 0x80000000 and k0 == 0)

    def var(label, bits):
        assert label not in w or w[label] == bits
        w[label] = bits
        return label

    def add(*names):
        a = sorted(set(q for q in names if q is not None))
        if len(a) > 1:
            f.append(tuple(a))

    def tag(label, bit):
        # Known-zero output tags can be constant folded in special case.
        if simple and label == "E0" and bit // 4 != 7:
            return None
        return var(f"{label}:{bit}",1)

    def d(j,i):
        if simple and j == 1 and i not in (1,2):
            return None
        return var(f"D{j}:{i}",4)

    def x(j,i):
        if simple and j == 0 and i != 7:
            return None
        return var(f"x{j}:{i}",4)

    # Local parallel base and perturbed carry chain with real S-box.
    for j in range(5):
        for i in range(8):
            if simple and j==0 and i!=7:
                continue
            x_i = x(j,i)
            if simple and j==0:
                cin=cout=None
            else:
                cin=var(f"C{j}:{i}",2) if i else None
                cout=var(f"C{j}:{i+1}",2) if i<7 else None
            digit_d=d(j,i) if 1<=j<=3 else None
            utags=[tag(f"U{j}",4*i+b) for b in range(4)] if 1<=j<=3 else []
            etags=[tag(f"E{j}",4*i+b) for b in range(4)]
            add(x_i,cin,cout,digit_d,*utags,*etags)

    # Wiring constraints. Each tag bit at source (pos-11)%32 contributes
    # to one rotated 32-bit bit; no whole-nibble overapproximation here.
    for pos in range(32):
        i=pos//4
        src=(pos-11)%32
        a=tag("E0",src)
        p=d(1,i)
        q=d(2,i)
        t=d(3,i)
        if a is not None:
            add(p,a)
        add(q,tag("E1",src))
        add(t,p,tag("E2",src))
        add(q,tag("E3",src))
        add(t,tag("E4",src))
        # x1=z XOR g1(r), x4=r XOR g2(z), x5=z XOR g3(x4)
        if not simple or i==7:
            add(x(0,i),x(2,i),tag("U1",src))
        add(x(3,i),x(1,i),tag("U2",src))
        add(x(4,i),x(2,i),tag("U3",src))
    return w,f,simple


def main():
    cli=argparse.ArgumentParser()
    cli.add_argument("--alpha",type=lambda x:int(x,0),default=0x80000000)
    cli.add_argument("--beta",type=lambda x:int(x,0),default=0x681e60a7)
    cli.add_argument("--key0",type=lambda x:int(x,0),default=0)
    a=cli.parse_args()
    w,f,simple=bit_network(a.alpha,a.beta,a.key0)
    result=dict(total_variables=len(w), factors=len(f),
                one_active_nibble_first_g=simple,
                estimates=[eliminate(w,f,method) for method in ("min-neighbor","min-fill")])
    print("FIVE_BIT_FACTOR_WIDTH",json.dumps(result,sort_keys=True))


if __name__=="__main__":
    main()
