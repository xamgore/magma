# Reflection factorization and exact-counting alternatives

Status 2026-11-04. User's intended direction is the reflected
composition Q = J o G_rev o G, NOT the overlapping-three-round
construction. Both have independent uses, but they must not be
conflated.

## The actual RFC 20..28 key schedule

The nine keys (indices in the eight-word master key) are:

    [4,5,6,7, 7,6,5,4, 3].

Let J(L,R)=(R,L), G=F_7 o F_6 o F_5 o F_4 (the first
four *ordinary* Feistel rounds, in time order), and
G_rev=F_4 o F_5 o F_6 o F_7 (the next four time-ordered
rounds, with key index sequence 7,6,5,4).
Their eight-round palindrome is E8=G_rev o G.

Every ordinary Feistel round F_k satisfies

    F_k^(-1) = J o F_k o J.

Hence G_rev=J o G^(-1) o J. The composition requested is

    Q = J o G_rev o G
      = G^(-1) o J o G.

Consequently Q o Q=id and its fixed states are exactly

    Fix(Q) = G^(-1)(Fix(J)),
    Fix(J) = {(t,t) : t is a 32-bit word}.

Thus |Fix(Q)|=2^32 for EVERY fixed RFC master key. This
is algebraic, not a conjecture, and the earlier
Magma/NinePlus/reflection_window20.py tested it already.

## Exact nine-round outer-count rewrite

The full nine-round schedule is E9=F_3 o E8.
Its output difference (0,b) forces the input difference
of the last Feistel round to be (b,0), regardless of its
base state and key 3. The last-round map is bijective.

So for every 32-bit a,b and every fixed master key,

    D9_E9((a,0),(0,b))
      = D8_E8((a,0),(b,0))
      = D_Q((a,0),(0,b)).

For a generic 64-bit input difference alpha the first
equality remains true with alpha unchanged. This is an
exact equality of fiber cardinalities; it is NOT a claim
that the left-side coefficient is zero.

The alternative 9->7 boundary deletion is also valid:

    D9_E9((a,0),(0,b))
      = D7_[5,6,7,7,6,5,4]((0,a),(b,0)).

The first six inner keys [5,6,7,7,6,5] form a separate
three-round palindrome; this gives a shorter reflection
decomposition with an extra final F_4. Neither is currently
a complete fast fixed-key DDT algorithm.

## Why the reflected composition may help

Since Q=G^(-1) o J o G, a witness for
D_Q(alpha,beta) can be characterized entirely by G:

    choose x and y with G(y)=J(G(x)),
    require G(y XOR beta)=J(G(x XOR alpha)).

Because G is a permutation, y is unique for each x.
These are two correlated instances of the SAME
four-round G, related by J. They may admit an efficient
bidirectional, memoized, or nibble-local paired evaluator.
The state pairs cannot be separated into ordinary scalar
four-round DDTs.

Involutive Q also gives the exact symmetry

    D_Q(alpha,beta) = D_Q(beta,alpha).

But this identity alone does not imply any nonzero
impossible differential, nor does the 2^32 fixed-point
count produce an all-key impossible endpoint.

## Tested

New deterministic replay:
    python3 Magma/Composition/palindromic_j_composition.py
    python3 Magma/Composition/reflection_toy_ddt.py

The full-width structural test checks 16 distinct random
256-bit master key vectors, 80 input/state pairs per
master (1280 pairs), Q=J o G_rev o G=G^(-1) o J o G,
Q^2=id, and pointwise D9-to-D8 target matching.
This is a test of the algebraic identity, not an
independent theorem proof. The prior
NinePlus/reflection_window20.py already has 2400 tests
and the exact fixed-point cardinality argument.

The 4-bit-word toy enumerates ALL 225 nonzero opposite
boundary endpoint pairs (a,0)->(0,b). Direct nine-round
Feistel, palindrome eight-round Feistel, reflected
involution Q, and the correlated two-G crossing
constraints reproduce identical counts for all 225.
The toy has 149 zero coefficients and 76 positive
coefficients at its ONE selected key; these do NOT imply
any 32-bit Magma universal impossibility claim.

Other new exact-counting experiments are documented in
OVERLAPPING_J.md. They solve a DIFFERENT 5=3+3-1
state-lifted overlap identity and do not by themselves
exploit the palindromic key schedule.

## Alternatives to benchmark (ranked by expected value)

1. Reflected four-round join, exact fixed keys.
   Express D_Q(alpha,beta) as two G executions linked
   by G(y)=J G(x), with real shared base and differences.
   Contract using bounded nibble-local carries and
   delayed rotation tags. The critical diagnostic is
   actual maximum symbolic factor/BDD width, not the
   number of satisfying examples.

2. A state-lifted old three-round J with conditional
   first/last-round constraints, rather than a scalar
   three-round DDT. Reuse Rust's tested local kernel,
   keeping an actual sufficient joint base/tag label.
   A two-J 3+3-1 overlap is a distinct, valid formula,
   but building its whole symbolic relation eagerly
   led to BDD expansion even for a two-S-box toy.

3. Compare mature exact knowledge/model counters
   against the SAME full Feistel CNF. Explore:
     Ganak: https://github.com/meelgroup/ganak
     d4: https://github.com/jm62300/d4
     DPMC / ProCount: https://github.com/vardigroup/DPMC
     ADDMC: https://github.com/vardigroup/ADDMC
   Ensure all Tseitin auxiliary variables are
   uniquely determined by the original plaintext
   pair (or use projected counting correctly).
   Otherwise counts can be inflated. Never turn
   UNKNOWN/LIMIT into UNSAT.

4. Project-join-tree / algebraic decision diagram
   contraction of local carry constraints rather
   than the current Python sparse relational join.
   Benchmark several elimination orders; measured
   factor widths beat speculative complexities.

5. Sound support-only early filters: exploit the
   key-independent bijectivity of g to infer that
   Delta_g(k,x,d)=0 iff d=0, and the resulting
   d_(i+2)=d_i iff d_(i+1)=0. Preserve fixed-key
   and universal-key distinctions in all claims.

6. Once a fast exact 7/9 core exists, compare genuine
   shared RFC key constraints with an artificial
   independent-key relaxation to identify reusable
   all-key rejections. No new nine-round bulk SAT
   sweep is authorized under the design freeze.

## Relevant methods and reading

- DPMC: Weighted Model Counting by Dynamic Programming
  on Project-Join Trees, Dudek/Phan/Vardi (2020):
  https://arxiv.org/abs/2008.08748
- ADDMC: Weighted Model Counting with Algebraic
  Decision Diagrams, Dudek/Phan/Vardi (2019/2020):
  https://arxiv.org/abs/1907.05000
- Exact model-counting competition implementation roster:
  https://mccompetition.org/solvers/solvers
- AutoDiVer: Automatically Verifying Differential
  Characteristics and Learning Key Conditions (2025):
  https://eprint.iacr.org/2025/185
- Lean kernel-approved bijection and reverse-key DDT
  identity: Magma/Diffan/FiveRoundDDTReverse.lean.
- Prior checked 8-round palindrome/involution:
  Magma/NinePlus/reflection_window20.py.

No aggressive optimization, broad nine-round SAT searches,
or unrelated Lean weight-aggregator proof work has been
unfrozen. The P0 is now a measured compressed conditional
join using the reflected schedule when relevant.
