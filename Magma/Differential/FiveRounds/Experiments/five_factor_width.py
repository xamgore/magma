#!/usr/bin/env python3
"""Structural width of a *fully correlated* five-g RFC Magma factor network.

Only analyzes factor scopes; it does NOT calculate a DDT.  Local input,
carry-pair, base S-box tag, derivative tag and rotated wiring variables are
separate, so no base correlation is silently replaced with a marginal DDT.
The induced-width estimate identifies why blindly enlarging the 3-g HashMap
frontier is dangerous. For cyclic rotate-left-11, output nibble i reads
source tag nibbles (i-3) and (i-2), modulo eight.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
import argparse
import json


def factor_graph(alpha, beta):
    widths = {}
    factors = []

    def var(name, bits):
        if name in widths:
            assert widths[name] == bits
        widths[name] = bits
        return name

    def add(*names):
        factors.append(tuple(sorted(set(names))))

    # base input x1,r,z,x4,x5, active derivative tags E0...E4,
    # and base output tags U1,U2,U3; carry pairs for five g's.
    for j in range(5):
        for i in range(8):
            x = var(f"x{j}:{i}", 4)
            e = var(f"E{j}:{i}", 4)
            u = var(f"U{j}:{i}", 4) if 1 <= j <= 3 else None
            c_in = var(f"C{j}:{i}", 2) if i else None
            c_out = var(f"C{j}:{i+1}", 2) if i != 7 else None
            d = var(f"D{j}:{i}", 4) if 1 <= j <= 3 else None
            # Exact dual-carry S-box step, with fixed a,b for j=0,4.
            # All pair-step outputs are functions of inputs; a factor is 0/1.
            add(*[q for q in (x, e, u, c_in, c_out, d) if q])

    for i in range(8):
        j3, j2 = (i-3)%8, (i-2)%8
        # derivative difference stream p=D1, q=D2, t=D3
        add(f"D1:{i}", f"E0:{j3}", f"E0:{j2}")
        add(f"D2:{i}", f"E1:{j3}", f"E1:{j2}")
        add(f"D3:{i}", f"D1:{i}", f"E2:{j3}", f"E2:{j2}")
        add(f"D2:{i}", f"E3:{j3}", f"E3:{j2}")
        add(f"D3:{i}", f"E4:{j3}", f"E4:{j2}")
        # Actual three Feistel base equations x1=z^g1(r), x4=r^g2(z),
        # x5=z^g3(x4). Keep the genuine output tags of every g.
        add(f"x0:{i}", f"x2:{i}", f"U1:{j3}", f"U1:{j2}")
        add(f"x3:{i}", f"x1:{i}", f"U2:{j3}", f"U2:{j2}")
        add(f"x4:{i}", f"x2:{i}", f"U3:{j3}", f"U3:{j2}")
    return widths, factors


def eliminate(widths, factors, method):
    graph = {v: set() for v in widths}
    for f in factors:
        for u in f:
            graph[u].update(set(f)-{u})

    max_bits = 0
    max_vars = 0
    records = []
    while graph:
        if method == "min-neighbor":
            key = lambda v: (sum(widths[w] for w in graph[v]), len(graph[v]), v)
        elif method == "min-fill":
            def key(v):
                neighbors = graph[v]
                n_list = list(neighbors)
                missing = sum(widths[n_list[i]]*widths[n_list[j]]
                              for i in range(len(n_list))
                              for j in range(i+1,len(n_list))
                              if n_list[j] not in graph[n_list[i]])
                return missing, sum(widths[w] for w in neighbors), v
        else:
            raise ValueError(method)
        v = min(graph, key=key)
        nb = graph[v]
        bits = widths[v]+sum(widths[w] for w in nb)
        max_bits = max(max_bits, bits)
        max_vars = max(max_vars, len(nb)+1)
        if bits >= 60 and len(records) < 8:
            records.append([v, bits, len(nb)])
        for n in nb:
            graph[n].update(nb-{n})
            graph[n].remove(v)
        del graph[v]
    return dict(method=method, peak_scope_bits=max_bits,
                peak_scope_variables=max_vars,
                naive_dense_entries_estimate=f"2^{max_bits}",
                first_large_scopes=records)


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--alpha",type=lambda s:int(s,0),default=0x80000000)
    p.add_argument("--beta",type=lambda s:int(s,0),default=0x681e60a7)
    a=p.parse_args()
    widths,factors=factor_graph(a.alpha,a.beta)
    result=dict(scope="structural upper-bound proxy, ignores table sparsity",
                variable_count=len(widths),factor_count=len(factors),
                rotation="rot11 nibble i = tag_(i-3)>>1 | ((tag_(i-2)&1)<<3)",
                estimates=[eliminate(widths,factors,m) for m in
                           ("min-neighbor","min-fill")])
    print("FIVE_FACTOR_WIDTH",json.dumps(result,sort_keys=True))


if __name__=="__main__":
    main()
