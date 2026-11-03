# Joint middle-base elimination: exact full Magma five-round fibers

Status: 2026-11-03. **Computational exact full fixed-key 5-round DDT
counts**, independently exhausted by Z3, using a jointly weighted
8-nibble transfer. The local accepted-word semantics are *proved in
Lean*; the Rust weighted-count ↔ witness-count correspondence is NOT
yet itself a kernel theorem. Nine-round SAT motif hunting stays frozen.

## Extension: general 64-bit three-round DDT (2026-11-03)

The SAME joint_middle_transfer.rs now accepts arbitrary
ordinary three-round input `(A,P)` and output `(T,B)`.
New flags `--core-input-left A` and
`--core-output-right B` default to zero; historical
`--alpha P`, `--beta T` are unchanged. Algebraically,
the first g output E determines second input
`Q=A XOR rot11(E)`; middle output is `P XOR T`
and third output `rot11(E) XOR A XOR B`. Both
cyclic S-box streams and six carry bits are still shared.

Independent full three-round Z3 and the generalized
Rust transfer give exact **48** for
`(0x12345678,0x9abcde12)->(0x216ed12f,0x3f6e53d2)`,
and exact **0** for the strict-correlation central block
`(0x80000000,0x00000580)->(0xa7018a3d,0x681e60a6)`.
All 15 old five-round DDT regressions still pass.
See [SEVEN_CORE.md](SEVEN_CORE.md) for the exact
derivative equations, fixed keys, and reproducible tests.

The new general three-round block does NOT yet compose
with the two outside genuine base states of the opposite
five-round core; this is the next targeted algorithmic task.

## The mathematical identity

For any three fixed 32-bit Magma round keys k1,k2,k3 and differences
a,b, introduce two genuine 32-bit intermediate base words r,z:

    c := g(k1,r XOR a) XOR g(k1,r)
    h := g(k2,z).

The exact triple-fiber constraints are:

    g(k2,z XOR c) XOR g(k2,z) = a XOR b
    g(k3,(r XOR h) XOR b) XOR g(k3,r XOR h) = c.

Each admissible (r,z) corresponds to **one actual plaintext**
for the outer five-round differential (a,0) -> (0,b), given
any fixed outer keys k0,k4. Its initial Feistel base is:

    original_right := z XOR g(k1,r)
    original_left  := r XOR g(k0,original_right).

Thus counting admissible (r,z) gives the **real fixed-key DDT
multiplicity**, not a product of marginal DDTs and not a count
of abstract differential characteristics.

## Algorithm: eliminate 32-bit middle word INSIDE the transfer

The earlier fixed_middle_transfer.py calculated C(h) at a
**fixed** h, then summed small subsets of 2^32 middle words.
The new joint_middle_transfer.rs makes BOTH local S-box tag
streams symbolic and keeps them jointly correlated:

    E_i : first g substituted XOR-derivative nibble
    U_i : middle g genuine BASE S-box output nibble

RFC rotate-left-11 gives, with nibble indices modulo 8,

    c_i = (E_(i-3) >> 1) | ((E_(i-2) & 1) << 3)
    h_i = (U_(i-3) >> 1) | ((U_(i-2) & 1) << 3).

At each of eight actual Magma S-box positions, the weighted
transition preserves **six carry bits** for three 32-bit
addition-derivative chains. It enumerates 4-bit base digits
r_i,z_i and enforces

    middle XOR output = nibble_i(ror11(a XOR b))
    third XOR output  = first XOR output

while the middle input difference c_i is derived from E
and the third BASE input r_i XOR h_i from U.

The cyclic boundary guesses E5 high3, E6 full4, E7 full4,
and the same 11 bits for U. Thus the full computation has
2^22 = **4,194,304 boundary seeds**; every genuine r,z
has exactly one such seed. Closure is enforced at nibbles
5,6,7. Each running state keeps six carry bits and six
recent full nibble tags (30 encoded state bits). Equal
states merge by **adding integer multiplicities**.
All sums are exact integers; no Markov independence, SAT
sampling, or heuristic truncation occurs inside the DP.

For h subcubes, the required mask on the rotated U output
is imposed within local transitions. With --free-bits 32,
h is **fully unconstrained** and the result is the FULL
five-round count, not an outer loop over 2^32 h values.

The Rust implementation uses only the standard library,
accepts custom --keys, --alpha, --beta and --reference-h,
and has strict limits on seeds, frontier, transitions and
runtime. A LIMIT is not an UNSAT result. Full counts fit
in u128 (at most 2^64 possible input base pairs).

## Two complete fixed-key five-round results

| Outer differences (a,0) -> (0,b) | Rust DP | Independent Z3 | DP time | Z3 time |
|---|---:|---:|---:|---:|
| a=0x00000080, b=0xC0000820 | **768** | **768** | 35.91 s | 0.69 s |
| a=0x80000080, b=0x20200020 | **30,720** | **30,720** | 6.65 s | 44.95 s |

The fixed five-round key vectors are in the source fixtures
and the independent verification reports. Outer keys k0
and k4 are zero in these tests; the outer DDT is independent
of their values.

The independent Z3 verifier models BOTH free 32-bit base
words r,z. It enumerates and blocks every satisfying pair,
reconstructs the corresponding concrete 64-bit initial
plaintext, directly replays all five Magma Feistel rounds,
and eventually receives **UNSAT**. This is exhaustion, not
a timeout. SHA-256 hashes of all sorted solutions are
recorded in joint_full_z3_0.json and joint_full_z3_1.json.

The peak full DP frontiers were **43,008** and **10,240**
states, exploring approximately 4.10 billion and 0.679
billion local edges. There is NO universal speed advantage
over Z3: in the first case Z3 is about 52x faster; in
the second the DP is about 6.8x faster.

### Partial-h exact regressions

Constrain all but the indicated LOW bits of h to the
original kernel-certified positive witness's value.

| Free low bits of h | h values | First fixture | Second fixture |
|---|---:|---:|---:|
| 0 | 1 | 16 | 96 |
| 4 | 16 | 48 | 288 |
| 8 | 256 | 96 | 576 |
| 12 | 4096 | 192 | 576 |
| 16 | 65,536 | 192 | 576 |
| 24 | 16,777,216 | 192 | — |
| 28 | 268,435,456 | 192 | — |
| 32 | 4,294,967,296 | **768** | **30,720** |

The 0-,4-,8-bit cases match the earlier fixed-h DP and
independently exhausted Z3 subcube counts. Each full
32-bit count matches unrestricted independent #SMT.
Intermediate 12/16/24/28 counts were not separately
exhausted by Z3.

A nonzero impossible endpoint regression for the first key,
a=0x00000080, b=0x00000001, gives complete DP **0**
and independent Z3 UNSAT. This is fixed-key evidence,
not by itself a universal all-keys ID theorem.

## Formalization status

- TaggedCarryWord.lean: actual eight-step carry tags rebuild g
  and its XOR derivative for arbitrary key/base/difference.
- Rotate11Nibble.lean: exact two-source nibble formula for
  RFC rotate-left-11.
- **JointTaggedAcceptance.lean (new):** general symbolic
  theorem jointTaggedAccept_iff_real proves that eight-nibble
  local tagged-acceptance is equivalent to the two correlated
  full-word derivative equations, for all 32-bit keys/bases.
- **Not yet kernel-proved:** Rust HashMap weighted aggregation
  and cyclic-seed uniqueness as a cardinality theorem.
  Counts above are *computationally* certified by independent
  exhaustive Z3 and direct Feistel replay.

## Reproduce

Compile with standard Rust:

    rustc -O -C target-cpu=native \
      Magma/Composition/joint_middle_transfer.rs \
      -o /tmp/magma_joint_middle_transfer

Full DDT:

    /tmp/magma_joint_middle_transfer --fixture 0 \
      --free-bits 32 --max-seconds 150 \
      --max-edges 18000000000 --max-frontier 250000

    /tmp/magma_joint_middle_transfer --fixture 1 \
      --free-bits 32 --max-seconds 150 \
      --max-edges 18000000000 --max-frontier 250000

Arbitrary keys and differences:

    /tmp/magma_joint_middle_transfer \
      --keys 0x2056,0xfdfa7789,0xf0f8d960 \
      --alpha 0x80 --beta 0x01 --free-bits 32

For smaller h subcubes also provide --reference-h and
--free-bits below 32. Re-run independent verification:

    python3 Magma/Composition/verify_joint_full_z3.py \
      --fixture 0 --expected 768 --model-cap 1000

    python3 Magma/Composition/verify_joint_full_z3.py \
      --fixture 1 --expected 30720 --model-cap 40000

    python3 Magma/Composition/joint_middle_regression.py --full

    lake build Magma

The regression rebuilds Rust, checks source SHA-256,
full UNSAT-exhausted independent reports, known slices,
both full counts, and independent zero-count feasibility.

## Next actual research barrier

The full 32-bit middle word h has been eliminated for
the five-round OUTER slice. The same weighted engine
now handles GENERAL three-round DDTs; the direct
five-round OPPOSITE core has independently verified
seven-round fixed-key counts (2, 0, 0). See
SEVEN_CORE.md for the precise constraints and inputs.

**Next active goal:** compose the general three-round
block with the genuine outer base/difference constraints
to calculate the opposite five-core efficiently.
General Rust weighted-bijection Lean formalization is
explicitly frozen by ROADMAP.md, as is bulk nine-round
SAT motif hunting. Only targeted independent Z3 checks
of new correlated composition are allowed.
