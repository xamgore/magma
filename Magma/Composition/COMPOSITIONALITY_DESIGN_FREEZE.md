# Compositionality and compact elimination: DESIGN FREEZE

**Frozen 2026-11-04. Priority: REUSABLE DIFFAN COMPOSITION, not
maximizing searched round counts or chasing isolated impossible cells.**

The source of truth is genuine fixed-key Feistel/bitvector semantics,
exact integer counts, actual base correlations, and complete/LIMIT
separation. Any future proposed shortcut must satisfy the gates below.

## 1. The one reusable mathematical object

For a transformation f between state spaces with selected difference
conventions, define the BASE-LABELLED deterministic derivative kernel

    T_f(x,alpha; y,beta) =
      [y=f(x)] [beta=Delta_f(x,alpha)]  in {0,1}.

The composition over the SAME full intermediate base and difference is

    T_(g o f)(x,a; z,c)
       = SUM_(y,b) T_f(x,a;y,b) * T_g(y,b;z,c).

This is exact. DDT_f(a,b) is a *terminal contraction* that discards
the original base; scalar DDT_f and DDT_g are not composable
without an additional exact factorization theorem. Existing
Diffan.WeightedKernel, KernelFactorization, LabelJoinDefect,
ChainCount, LocalTransducer and StateDifference cover much
of the abstract framework. Do not duplicate them.

**New universal geometry theorem:**
Diffan/ConjugatedDifferenceSpace.lean defines an EXACT
pullback of ANY Diffan.DifferenceSpace along an equivalence
e:X~Y and proves the integer DDT conjugation law when the
difference convention is pulled back on BOTH sides.
For XOR and a nonlinear change of coordinates, holding
the original XOR geometry fixed invalidates that shortcut.

**New exact twisted self-Gram operator:**
Diffan/TwistedConditionalGram.lean proves for arbitrary
finite base-label U, derivative-label D, deterministic response
t:U->A->D and arbitrary base/difference actions sigma,tau:

    Gram_t(a,b) =
      SUM_(u,lambda) [t(u,a)=lambda]
                    *[t(sigma(u),b)=tau(lambda)]
    = SUM_u [t(sigma(u),b)=tau(t(u,a))].

The last equality eliminates lambda EXACTLY; it is not a
stochastic assumption. All calculations are in Nat.

## 2. Magma reflection specializes the shared operator

RFC ordinary Feistel rounds 20..28 use master-key word indices
[4,5,6,7,7,6,5,4,3]. For arbitrary k0,k1,k2,k3 and
independent last key, H is the first FOUR rounds,
J(L,R)=(R,L), and Q=H^{-1} J H.

Define the *single reusable* four-round conditional operator

    t_H(u,alpha) =
      H(H^{-1}(u) XOR alpha) XOR u.

Then the exact integer DDT of Q for ANY 64-bit XOR
differences alpha,beta is the twisted self-correlation

    D_Q(alpha,beta)
      = SUM_(u,lambda)
          [t_H(u,alpha)=lambda]
          [t_H(Ju,beta)=Jlambda]
      = SUM_u
          [t_H(Ju,beta)=J(t_H(u,alpha))].

Written formally T_H^T P T_H, where the involutive
permutation P sends (u,lambda) to (Ju,Jlambda).
This immediately explains the exact D_Q symmetry.

Lean theorems:
 - Magma.DiffanNineReflection.Q_ddt_in_adapted_coordinates
 - Magma.DiffanNineReflection.qDDT_eq_twisted_conditional_gram
 - Magma.DiffanNineReflection.nine_ddt_eq_twisted_four_round_gram
 - earlier nine_ddt_eq_fourCrossingMass (explicit pair bijection)
 - earlier Q_has_exactly_two_pow_32_fixed_points

The nine-round opposite-boundary DDT equals this self-Gram
at alpha=(a,0), beta=(0,b); the last Feistel key drops out.
The new theorem is a BASIS FOR CACHING, compositionality
and future exact contraction, NOT an algorithm that materializes
the astronomically large Gram matrix.

## 3. Local exact carry/tags — no missing cross-round coupling

Current executable baseline:

    Magma/Composition/reflected_four_local_join.py

Let stream S be X (base x, perturbed x XOR (a,0)) or
Y (base y, perturbed y XOR (0,b)).
For each stream, four Feistel rounds use two six-word
sequences X0..X5 or Y0..Y5 and corresponding XOR
difference words dX0..dX5 or dY0..dY5, with

    X_(j+2)  = X_j XOR ROL_r(U_j)
    dX_(j+2) = dX_j XOR ROL_r(E_j)

(and identically for Y). Input difference words are
dX0=a, dX1=0; dY0=0, dY1=b.

At nibble i of round j, for fixed key digit k,
real base nibble s, real XOR difference digit d,
and the TWO addition carry-in bits c,c':

    z  = s + k + c
    z' = (s XOR d) + k + c'
    U  = S_i(z mod 16)
    E  = U XOR S_i(z' mod 16)
    c+  = floor(z / 16)
    c'+ = floor(z' / 16).

The *same* U,E tags are rotated into both the
next base and next XOR difference. The initial
carry-in bits at the least significant digit are
zero. Final carry-outs are discarded (mod 2^w).
ROL_r accesses exactly the source bits
(pos-r) mod w, including cyclic wrap-around.

Do NOT multiply independent DDTs, choose separate
keys for reflected streams, or project away an
active real base word. All S-box tables are the
actual RFC S-boxes 0..nibbles-1.

The two reflected output crossings are implemented
as IDENTIFICATION of shared variables, for every
nibble i:

    Y4[i]  = X5[i],   Y5[i]  = X4[i]
    dY4[i] = dX5[i],  dY5[i] = dX4[i].

No independent y enumeration is retained after this
junction: for every real initial x, the first
base crossing uniquely reconstructs y=Q(x).
All carry and U,E assignments are then functional,
giving a one-to-one correspondence between satisfying
CSP assignments and real input bases. Thus full
integer Nat-semiring elimination is an exact DDT,
without overcounting Tseitin/gate variables.

## 4. Honest measured gates

The 4-bit / ONE-Sbox model has 32 local variables
and 24 factors for each boundary query. All 225
nonzero (a,b) cells for fixed key (5,6,7,8) were
counted exactly with sparse weighted elimination
and compared to an INDEPENDENT direct 9-round
exhaustive Feistel implementation:

    225/225 exact
    149 zero entries, 76 positive entries
    SUM selected counts = 188
    maximum sparse intermediate factor = 4,096 rows
    total ~7.1 seconds

Also checks positive counts 2 and another 2, and zero 0,
across two key vectors.

The 8-bit / TWO-Sbox model has 72 variables and 48
factors. Direct nine-round exhaustive reference for
keys (1,2,3,4), a=1,b=0xd7 is 0. Generic sparse
elimination returns LIMIT at 250,000 rows after
20-24 of 72 eliminated variables. A one-nibble
Shannon cutset Xu0:0=0 still returns LIMIT.
No 8-bit exact result via the sparse factor engine
has been claimed. Independently, Z3 four-crossing
and Z3 direct nine both complete that toy zero
(with ~2s and ~4.4s on different runs; this is
NOT a stable comparative speed guarantee).

Full 32-bit RFC factor graph has 312 symbolic
variables and 192 *local* factors after crossing
variable identification and constant endpoint
simplification. Heuristic min-neighbor/min-fill
elimination of its scopes yields peak *DENSE*
scopes of 218/238 bits. These are upper bounds
for the tested orders only, NOT a complexity lower
bound, NOT sparse factor row counts, and NOT an
operationally viable full-width elimination.
No full 32-bit weighted nine-round count has
been calculated.

See reflected_four_local_regression.py for
reproducible exact/limit gates.

## 4a. Proof-of-concept multi-query caching of ONE H kernel

`twisted_four_cached_kernel.py` materializes conditionalH
for a tiny toy state space once per requested input-difference
label and then answers an entire grid of endpoint DDT queries
by the proved twisted self-Gram relation, with NO additional
Feistel evaluations in the join. The same actual fixed
four-round key vector is reused in all columns.

4-bit one-Sbox toy, keys (5,6,7,8), all 225 nonzero
opposite boundary pairs:

    30 cached input-difference labels (15 left,15 right)
    256 actual 8-bit base states per label
    cache preparation + all joins: 0.0188s
    independent 9-round brute all pairs: 0.3538s
    observed toy speed ratio: ~18.8x
    all 225 counts exact, 149 zeros/76 positives/sum 188.

8-bit two-Sbox toy, keys (1,2,3,4), alpha=1 and
beta in (1,0xd7,0x80,0xff):

    5 cached input-difference labels
    65,536 actual 16-bit base states per label
    cache preparation + four joins: 0.9293s
    independent 9-round brute same four pairs: 2.06s
    observed toy speed ratio: ~2.2x
    all 4 counts exact, 2 zeros/2 positives/sum 4.

Timings are individual runs, not a reproducible performance
guarantee. The cache *does not* become feasible at 32-bit
word size: it would need 2^64 actual base states per
input-difference label. The high-value next step is replacing
these concrete base arrays by the same symbolic, exact
paired-carry/rotation conditional kernel with a compressed
live frontier (ADD/BDD/transfer).

This small-cache result confirms the *multi-query leverage*
of the algebraic Gram factorization rather than claiming
any new differential characteristic.

## 5. Frozen next computational design: frontier first

**Only promote an optimization if it composes the one-H
conditional kernel while preserving local dual carries,
both real base histories and both rotated tag streams.**

Planned subproblems, in this order:

1. Derive an actual graph separator B_i as exactly the
   wires touching both processed and unprocessed factors.
   Eliminate each local input/base/carry/tag variable
   immediately after its LAST constraint occurrence.
   Use the weighted interface
        W_i(b) = SUM_hidden PRODUCT_local_factors,
   with weights in Nat and exact wire agreement.
2. Address cyclic ROL11 via a bounded FRONTIER
   of overlapping low-order tag bits. Conditions
   on an output tag are disjoint Shannon branches;
   summing COMPLETE branches is exact. One
   isolated nibble condition was not enough.
   Never enumerate 2^176 naive independent tag
   seeds or claim it is the minimal frontier.
3. Consider hash-consed ADD/ROBDD semiring factors and
   functional-dependency substitution (e.g. when
   next base/difference is uniquely determined by
   current base and g tags). The current generic
   sparse HashMap join is NOT a successful answer.
4. Exploit the same H conditional kernel in the
   Gram self-join: cache its symbolic factor DAG and
   apply P to its (u,lambda) interface rather than
   rebuilding unrelated round models. Numeric
   multiplication of marginal four-round DDT
   entries is FORBIDDEN.
5. Measure FULL graph max live separator size and
   max compressed diagram nodes, plus actual exact
   integer counts. The target first gate is a
   COMPLETE 8-bit two-Sbox carry-factor count in
   a bounded budget, independently reproduced.
   Only then promote to 12/16-bit comparisons,
   then real 32-bit controls.

A generic typed DDT framework cannot make a fixed-width
S-box/carry implementation automatically work for all
difference notions. Instantiate a concrete DifferenceSpace
and prove the appropriate local gate semantics separately.

**SAT rule:** per-case Z3 timeout up to 600 seconds is
allowed by the user, but this is a ceiling, not a
licence for untargeted bulk search. Declare controls,
compare the SAME semantics and keys, replay every SAT
model, and treat UNKNOWN/LIMIT as neither zero nor
positive. Structural representation improvements, not
more SAT runtime, are the immediate P0.

## 6. Stop/go acceptance tests

 - Lean: no sorry/admit; #print axioms clean of native
   bv_decide for the generic and reflection-Gram
   composition theorems.
 - Toy: all 225 four-bit boundary cells exact.
 - Carry: each real base and its XOR-partner use
   the SAME key and independently propagated
   carry-in bit, with initial zero/final discard.
 - Count: all auxiliary tags and carry witnesses
   are uniquely determined; no projected count inflation.
 - False join: each imposed shared boundary label
   must correspond to a real base/difference wire
   or have a proved sufficient-statistic certificate.
 - Limits: any failed branch/row/time cap => LIMIT,
   with NO total DDT value.
 - Complexity: promote only measured peak-factor or
   compressed-frontier improvements; no unproved
   assertion of a tractable 32-bit algorithm.

## Reproduce

    lake build Diffan.ConjugatedDifferenceSpace
    lake build Diffan.TwistedConditionalGram
    lake build Magma.Diffan.NineReflection
    lake build Magma
    python3 Magma/Composition/reflected_four_local_regression.py
    python3 Magma/Composition/twisted_four_cached_kernel.py --nibbles 1
    python3 Magma/Composition/twisted_four_cached_kernel.py --nibbles 2
    python3 Magma/Composition/reflected_four_local_join.py --structure32
    python3 Magma/Composition/reflected_four_conditioning.py --variable Xu0:0 --branch-count 1 --seconds 6

The earlier universal 1,908,225 seven-round zero
pairs remain valid and separately proved in Lean.
They are not used to infer a nine-round impossibility.
