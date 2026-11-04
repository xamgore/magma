# Two overlapping J kernels: exact composition and its limits

Status: 2026-11-04. Research experiments, real 32-bit Magma SMT
cross-checks and independent toy binary decision diagram counters.
No new fast 32-bit weighted five-chain DP or universal nine-round
impossible differential is claimed.

## 1. No nonzero input difference can make Delta g zero

For fixed key k, RFC Magma g_k(x)=rol11(S(x+k mod 2^32)).
All eight four-bit S-boxes are permutations, as are modular key
addition and rotation. Therefore g_k is a bijection and

    g_k(x XOR d) XOR g_k(x) = 0  <=>  d=0.

The explicit inverse is

    g_k^(-1)(y) = S^(-1)(ror11(y)) - k  (mod 2^32).

For the genuine Feistel difference recurrence this means

    d_(i+2)=d_i  <=>  d_(i+1)=0

for ANY fixed round key. The same x+d=x idea under modular
addition also forces d=0. A zero right half can result from XOR
cancellation of TWO NONZERO quantities; it does not require a
zero g derivative.

For the opposite five-round core

    (d0,d1,d2,d3,d4,d5,d6)=(0,a,p,q,t,b,0),

a!=0 and b!=0 imply p!=0 and t!=0. If q=0 then p=t.
These are key-independent necessary internal constraints, but
do not alone establish a new all-key impossible endpoint.
The already verified positive seven-round solutions have
q=0x5be38062, hence this specific positive case is not in q=0.

Reproduction: magma_permutation_probe.py checks all eight RFC
S-box permutations and tests 1792 deterministic 32-bit inverse
and nonzero-derivative cases. This is implementation regression,
not a replacement for the direct algebraic proof.

## 2. Exact five rounds from two lifted 3-round J predicates

Let F_k be the genuine 64-bit Feistel permutation. For fixed
keys k0..k4, write

    P = F_k1 o F_k0,  C = F_k2,  Q = F_k4 o F_k3.

The real five-round permutation is Q o C o P.
Take an arbitrary 64-bit starting XOR difference alpha and
target XOR difference beta.

Let u be the WHOLE 64-bit base state after P, delta its XOR
difference, and gamma the XOR difference after the SHARED
middle round C. Define

    L_alpha(u,delta,gamma) =
      [delta = P(P^(-1)(u) XOR alpha) XOR u] *
      [gamma = C(u XOR delta) XOR C(u)]

    R_beta(u,delta,gamma) =
      [gamma = C(u XOR delta) XOR C(u)] *
      [beta = Q(C(u XOR delta)) XOR Q(C(u))].

Here [property] is a 0/1 truth indicator, not an already
summed ordinary differential probability.

Then the EXACT five-round multiplicity is

    D5_K(alpha,beta) =
       SUM_{u,delta,gamma} L_alpha(u,delta,gamma)
                           * R_beta(u,delta,gamma).

This is a 3 + 3 - 1 decomposition with overlapping
windows (k0,k1,k2) and (k2,k3,k4). The center C appears
in both local predicates only as the SAME 0/1 condition,
so it is not counted twice. Proof: each real starting
base x determines the unique u=P(x), delta, gamma. The
joint predicate is 1 iff the actual 5-round difference
is beta. Conversely every u determines exactly one x.

The OLD J was an ordinary scalar three-round DDT after
summing away all 64-bit bases. It is not a state-labelled
kernel. The new formula cannot be implemented by simply
multiplying those old scalar coefficients.

## 3. Scalar-J independence is a demonstrable false join

Write N=2^(2w), where w is the Feistel word width. Let
L3,C1,R3 be the ordinary DDT matrices for left three
rounds, the shared central round, and right three rounds.

One tempting but UNJUSTIFIED approximation is

    naive(alpha,beta) = (1/N^2) *
       SUM_{delta,gamma}
          L3(alpha,gamma) C1(delta,gamma) R3(delta,beta).

On a 4-bit-word Feistel toy (first RFC S-box, rotl1,
keys [1,2,3,4,5]), exhaustive tests for all 225 nonzero
opposite boundary cases (0,a)->(b,0) found:

- Exact lifted 3+3 agreement with exhaustive 5-round Feistel:
  225 / 225.
- Naive scalar-DDT expression disagreed: 225 / 225.
- 136 of those cases had exact D5=0 but the naive product >0.
- For a=b=1, exact 0 versus naive 82304/65536.

This refutes the displayed independence factorization,
not every possible clever manipulation of scalar matrices.
Reproduce with overlap_two_j_probe.py.

## 4. Why reversed keys and swapping tuples do not solve orientation

Let T(L,R)=(R,L). For Feistel,

    F_k^(-1) = T o F_k o T
    F_K^(-1) = T o F_reverse(K) o T,

so every fixed-key permutation has DDT symmetry

    D_K(alpha,beta) = D_reverse(K)(T(beta),T(alpha)).

In particular

    D5_K((0,a),(b,0)) =
       D5_reverse(K)((0,b),(a,0)).

The reverse problem STILL has opposite orientation.
Swapping the tuples does not reduce it to the old solved
outer five-round problem.

Conversely D5((a,0),(0,b)) is already efficiently counted
by the old J via exact deletion of its two zero-half
boundary rounds. The genuinely OPEN seven-round inner
problem is D5((0,a),(b,0)).

The full 256 by 256 toy DDT table was verified against
the reverse-key and swapped-half identity.

## 5. Exact real 32-bit Magma two-J regression

overlap_two_j_real.py independently constructs a symbolic
SMT equation at full shared state u=(r,z). It inverts
k0,k1 from u and runs k2,k3,k4 forward, sharing the actual
central state and difference. Models are blocked by (r,z),
replayed with genuine five-round Feistel and enumerated to
terminal UNSAT. Exact pair-set SHA-256 values equal existing
reference reports for all four cases:

| Opposite five-round fixed-key control | Lifted two-J #SMT | Reference |
|---|---:|---:|
| a=0x80000000 b=0x681e60a7 | 2 | 2 |
| a=0x00000001 b=0x00000001 | 0 | 0 |
| a=0x80000000 b=0x681e60a6 | 0 | 0 |
| Nonzero outer keys: a=0x80000000 b=0x1d43093d | 8 | 8 |

This checks correctness of composition, not the speed
of a future non-SMT weighted carryDP. The first three
five-core results imply the respective fixed-key seven-round
results by the already proved boundary-round deletion.

## 6. Sound projected support filters and their failures

overlap_j_projection.py retains BOTH full intermediate
difference tuples delta,gamma, but varies how many raw low
bits of the shared base u survive a support projection.

The 4-bit-word toy has 8-bit full state u. A positive in
this projected join is only a NECESSARY-support witness.
No real witness is ever lost, but false joins can remain:

| Retained low bits of u | False-positive zero endpoints / 136 |
|---|---:|
| 0 | 136 |
| 1..4 | 136 |
| 5 | 130 |
| 6 | 112 |
| 7 | 55 |
| 8 | 0 |

This is a diagnostic for one raw-bit projection on a toy,
not a minimum-state-size theorem for Magma. A more meaningful
derived sufficient statistic might compress much better.

## 7. Exact BDD representation: encouraging toy, clear barrier

overlap_j_bdd.py stores the FULL 24-bit labelled relation
(u,delta,gamma) as a reduced ordered binary decision diagram
(ROBDD). It intersects the TWO lifted J relations and model
counts their AND over all shared bits. This is an independent
non-SMT exact counter, not a product of marginal DDT values.

For all 225 toy endpoints the computed exact DDT agrees with
the independent brute-force count. The BDD manager allocated
19,424 nodes for grouped variables, or 32,845 with the
tested bit-interleaved ordering. All 24 interface bits remain;
only their REPRESENTATION is compressed. Here the initial
J relations are still enumerated in the small toy.

overlap_j_circuit_bdd.py avoids that enumeration. It builds
a BDD directly from the actual fixed-key addition carry
logic, S-box Boolean functions and Feistel inverse/forward
circuits. Several four-bit cases finish, including the full
zero-input mass 256. With eight-bit words and two RFC S-boxes,
the simple circuit construction hits resource LIMIT at
500,000 nodes under both tested orders. Fixing up to eight
bits of the first shared base word still hits a 200,000-node
LIMIT. No complete 8-bit symbolic circuit case is claimed.

This suggests a specific P0: do NOT materialize the two
whole-block J relations or build monolithic Boolean
compositions. Derive a nibble-local shared carry/tag
boundary and contract the two lifted J blocks using
bounded symbolic factors (BDD/ADD or another representation).
Benchmark its actual width and complete DDT counts against
the independent reference cases 2,0,0,8.

## Reproduce

    python3 Magma/Composition/magma_permutation_probe.py
    python3 Magma/Composition/overlap_two_j_probe.py
    python3 Magma/Composition/overlap_j_projection.py
    python3 Magma/Composition/overlap_j_bdd.py
    python3 Magma/Composition/overlap_two_j_real.py
    python3 Magma/Composition/overlap_j_circuit_bdd.py --max-nodes 150000
    lake build Magma

Formal Rust-weight proofs, premature Rayon refactoring and
bulk nine-round SAT searches stay frozen. A fixed-key zero
is not an all-key impossible differential. The big-picture
goal remains correlated fixed-schedule composition and new
reusable key-universal impossibility criteria for 9+ rounds.
