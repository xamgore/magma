# Full RFC 8891: exact recombination of HALF-ZERO differential slices

Date: 2026-11-05. This restores the ORIGINAL research goal:
**ONE fixed secret 256-bit master key, freely chosen plaintexts,
observed ciphertexts, and computation/reuse of differential kernels
of the true 32-round Magma permutation**. No related-key oracle or
attack claim is assumed.

The engineering freeze on sparse carry/ADD/BDD/SAT optimizers is
unchanged. We have formal structural identities and exhaustive
small-model checks, not a sub-2^64 exact full-width DDT algorithm.

## 1. The endpoint slice is mathematically privileged

Let W=BitVec32, X=W×W. Let the actual XOR derivative
of a state map f be d_f(x,alpha)=f(x XOR alpha) XOR f(x).

The suggested exact half-zero differential slice is:

    S_K(a,b) = D_C32,K( (a,0),(0,b) ),

with all a,b in W (including 0 only when stated).

For every actual ordinary Feistel G_k with real
modular addition, Sboxes and rotation,

    d_Gk((L,R),(a,0)) = (0,a),

for ALL k, L, R and a. Thus the left-zero-INPUT
class is mapped deterministically onto the
right-zero-OUTPUT class by one G.

This is proved in Magma/Differential/FullCipher/Full32SlicedJoin.lean:
  one_round_half_zero_free.

It is important NOT to assert closure through 2+ rounds.
A right-zero input delta=(0,b) normally produces
(b, Dg(R,b)), whose two words can both be nonzero.

## 2. EXACT composition through the 16/16 midpoint

Write the 8-round forward block H using the SAME eight
32-bit master-key words 0..7; let J swap halves.
The true native RFC cipher (including its final GStar)
obeys

    C32 = Q16 o H²,
    Q16 = H^-1 o J o H.

Let F=H² and Q=Q16, and let u=F(x) be the true
intermediate base at the 16/16 cut.

The midpoint difference is a *function* of u and alpha:

    mu_F(u,alpha)
       := F(F^-1(u) XOR alpha) XOR u.

It is NOT a marginal DDT value sampled independently
of the midpoint base. The exact full-width identity is

    D_C32(alpha,beta) =
       SUM_{u in X} [ d_Q(u,mu_F(u,alpha)) = beta ].

In particular, the exact user's slice is

    S_K(a,b) =
       SUM_u [
          d_Q(u,mu_F(u,(a,0))) = (0,b)
       ].

The 16/16 prefix/suffix have the SAME genuine key words
and the SAME joined base u, with no re-keying.

The generic exact mathematical theorem is
Diffan/Composition/ExactBaseJoin.lean:
  intermediateDelta
  witnessEquiv
  ddt_comp_eq_exactBaseJoin
  exists_mu_eliminates.

The full REAL RFC specialization, linked to genuine
roundKey, master key, encrypt and final GStar, is
Magma/Differential/FullCipher/Full32SlicedJoin.lean:
  forward16
  native_32_eq_two_middles
  c32_ddt_eq_base_join
  c32_half_zero_slice
  rfc_c32_half_zero_slice
  midpoint_base_and_delta.

This ELIMINATES an auxiliary difference mu completely;
it does NOT eliminate the 64-bit midpoint base u.
There are no 2^128 independent (u,mu) choices.
A 2^64 sum is still far too large for exact full-width
evaluation without a new compression theorem.

## 3. Fatal error: zero-half projection INSIDE the cut

Define disjoint NONZERO intermediate difference types:
  L=(a,0), a!=0;
  R=(0,b), b!=0;
  M=(a,b), a!=0,b!=0.

A true difference of a permutation with nonzero input
never becomes the zero pair. Therefore an exact join
can be partitioned into L+R+M contributions, but
the M part must NOT be silently discarded.

The formal theorem clippedCount_le_actual says
restricting the 16-round midpoint to L or R never
increases the true DDT. Equality is NOT guaranteed.

Independent full 32-round one-Sbox toy:
- word width 4 bits, total state 8 bits;
- genuine single RFC Sbox, modular sum, ROL1;
- eight keys 1,2,3,4,5,6,7,8 in real
  chronological key schedule H|H|H|reverse(H);
- RFC final no-swap applied.

Over EVERY 225 nonzero half-zero endpoints a,b:
  81 DDT coefficients are positive;
  210 genuine ordered base-state witnesses;
  exact full-C DDT and conditional 16+16 join
  AGREE FOR ALL 225 COEFFICIENTS.

Of the 210:
  after  8 rounds: 192 have BOTH delta words nonzero;
  after 16 rounds: 194 have BOTH delta words nonzero;
  after 24 rounds: 170 have BOTH delta words nonzero.

At the 16-round cut, a zero-half-only projected join
retains just 16/210 (7.619%) and LOSES 194/210 (92.381%)
of the TRUE differential mass. In particular:

    S_toy(1,4) = 2
    cut16_projected_S_toy(1,4) = 0.

This is a concrete FALSE IMPOSSIBLE DIFFERENTIAL produced
by the naive projected approach. It is a toy regression,
not a full-width counterexample for that exact key.

Reproduce:
  python3 Magma/Differential/FullCipher/Experiments/full32_halfzero_slice_join.py

## 4. POSITIVE: compute other differential TYPES on half-zero slices

The user explicitly allows any differential type, not just
one specified (a,b). The output-right-AGGREGATE

    R_K(a) = SUM_{b in W} S_K(a,b)

has an exact and simpler state-count formula:

    R_K(a) = #{ (L,R) in W² :
       C32,K(L XOR a,R).left = C32,K(L,R).left }.

This is a **fixed-key chosen-plaintext collision**
statistic of ONLY the left OUTPUT HALF, with no
need to retain or enumerate individual output
difference labels b. It is publicly testable
by paired encryptions at (L,R),(L XOR a,R).

A GENUINE Lean theorem for the REAL native RFC
encrypt API proves this exact natural-number equality:

  rfc_full32_halfzero_aggregated.

Its generic proof uses outputLabelFiberEquiv and
sum_output_label_eliminates from
Diffan/Observables/SlicedCollisionEnergy.lean. There are no
independent differential characteristics.

If we additionally sum over all input differences a,

    E_K := SUM_{a,b in W} S_K(a,b),

then reparametrize L'=L XOR a. Write

    m_K(r,y) := #{ L : C32,K(L,r).left = y }.

The AGGREGATE COLLISION ENERGY identity is

    E_K = SUM_{r,y in W} m_K(r,y)^2.

Proof: each a is in bijection with L' at fixed L;
b is uniquely determined by the two right output
words, provided left output words match; then
group all (L,L') by their common left output y.

Diffan/Observables/SlicedCollisionEnergy.lean formally proves
the generic final group-by/fiber-square part:
  collision_energy_eq_fiber_squares.

The reindexing of a,b into (L,L') is elementary and
reproduced exhaustively in the full-32 toy
for every coefficient; that PARTICULAR all-a/all-b
equality is not yet a separate Lean theorem.
Do not overstate this audit boundary.

Toy numerical check:
  E=466 = 256 trivial zero-difference states
        + 210 genuine nonzero a,b witnesses
        = SUM_{r,y} m(r,y)^2.

Computational interpretation:
- To compute one row aggregate R(a) from a full
  ciphertext codebook, scan 2^64 states, compare
  ONLY 32 left output bits; no output b-table.
- To compute E from the full codebook, build
  32-bit projected output multiplicities for
  one input right word r at a time and sum squares.
  This avoids constructing the HUGE 2^64
  (a,b)-slice matrix.
- The full exact RFC 2^64 codebook is STILL
  unavailable at practical cost. The theorem
  improves DATA REPRESENTATION/REUSE, not
  automatically the asymptotic encryption count.

For an IDEAL uniformly random permutation of a
2w-bit block, for nonzero a and any input state x,
the probability the left w output bits agree
between F(x) and F(x XOR(a,0)) equals

    (2^w-1)/(2^(2w)-1) = 1/(2^w+1).

Thus E[ R(a) ] = 2^(2w)/(2^w+1) and the
expected aggregate NONTRIVIAL energy is
  2^(2w) * (2^w-1)/(2^w+1).
These are expectations over the ideal permutation,
not fixed-cipher equalities.

### Chosen-plaintext birthday sampling without known key

For q DISTINCT chosen left words L_i at ONE fixed right input R,
query C_K(L_i,R) and group the 32-bit LEFT ciphertext words.
Every collision pair yields BOTH a=L_i XOR L_j and
b=C_K,right(L_i,R) XOR C_K,right(L_j,R), so this
is an observable sample of the (a,0)->(0,b) slice
from a single unchanged secret key.

A uniformly random 64-bit PERMUTATION has probability
p=(2^32-1)/(2^64-1)=1/(2^32+1) that the left halves
of two DISTINCT ciphertexts agree. Therefore
    E_ideal[unordered collision pairs] = binom(q,2)/(2^32+1).
At q=2^16 the expected count is about 0.5.
At q=2^18 it is about 8. This is a birthday
observation with ~2^16 encryption queries, not a
single-key DISTINGUISHER: ideal permutations also collide.

A falsifiable next hypothesis must involve a biased
DISTRIBUTION of the observed a,b labels or a joint
multicollision statistic under an experimentally
or theoretically justified comparison to the ideal
permutation. A high ordinary collision COUNT alone
is not evidence of a structural weakness.
For a FIXED prescribed nonzero a, the projected
collision probability per queried input pair
is still ~2^-32, so aggregation across differences
is central to the cheap observable.

An INDEPENDENT 600-key one-Sbox toy comparison:
  Magma-schedule mean nontrivial energy: 226.0467
  random-permutation mean:              224.8867
  exact ideal expectation:              225.8824
  standard deviations: ~20.20 both.

There is NO observed dramatic full-32 toy bias
in this particular aggregate. No unknown-key
full-width distinguisher is claimed.

## 5. What the next mathematical gate REALLY is

We now have THREE precise objects, all for one
fixed master key:

1. Individual entries S_K(a,b):
   exact 16+16 base-conditioned join, full real RFC.
2. One-output-word aggregate R_K(a):
   exact collision condition on a 32-bit output
   projection, full real RFC.
3. Fully summed energy E_K:
   exact squared fiber multiplicities, all 32 rounds.

The next meaningful advance is a CERTIFICATE of
some actual compression of the state-indexed
midpoint kernel, or a proven low-rank/sparse
description of the 32-bit projected collision
fibers, respecting modular carries and the
identity of all shared base words.

Without such a certificate, replace repeated
2^64 sums by no more than a change of notation.
It is correct to freeze the expensive variable
elimination and search first for an algebraic
compression theorem. Experimental finite-width
cross-checks should distinguish real carry
semantics from the toy word width.

NO independent DDT multiplication.
NO zero-half restriction on internal cuts.
NO false full-32 impossible differentials.
NO artificial key changes.
NO implication of cryptanalytic break without
a publicly testable deviation against an
ideal random-permutation baseline.

Formal verification completed 2026-11-05:
  lake build Diffan Magma PASSED (18,755 jobs).
  Python full-32 one-Sbox toy tests PASSED (225
  boundary entries, 210 real witnesses, three cuts,
  full aggregation/histogram equality, 600-key
  vs 600 independent-random-permutation controls).
  #print axioms for ELEVEN new generic and native
  32-bit RFC statements reports ZERO sorry and
  ZERO native bv_decide reflection axioms.
  Only Lean standard propext/Classical.choice/
  Quot.sound appear as applicable.

Reproduction:
  lake build Diffan Magma
  python3 Magma/Differential/FullCipher/Experiments/full32_halfzero_slice_join.py
  lake env lean /tmp/AuditHalfZeroJoin.lean
