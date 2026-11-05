# Key-universal seven-round high-nibble impossible differentials

Status: 2026-11-04. Real RFC 8891 Magma, all independent 32-bit
round keys. New full Feistel theorem in
Magma/Differential/SevenRounds/SevenTopNibbleImpossible.lean. This is a genuine
KEY-UNIVERSAL family, not fixed-key enumeration.

The 225 high/high cases are a subset of the broader
**1,908,225 key-universal impossible seven-round endpoints**
identified by the first-active-nibble valuation obstruction
in [NIBBLE_VALUATION_FAMILIES.md](NIBBLE_VALUATION_FAMILIES.md).
**The broader family is NOW also a Lean theorem.**
SevenNibbleValuationClasses.lean proves all six classes for
all independently chosen round keys using the existing
certified first-active-nibble invariant, finite symbolic
bv_decide closure, and genuine Feistel-state equivalence.
Standard bv_decide native proof-reflection trust caveats
apply to both proofs.

## Exact mathematical claim

Let H = 0xF0000000, L = 0x0FFFFFFF,
R = 0x00000780, and C = 0xFFFFF87F
(the 32-bit complement of R).

For any nonzero words a,b supported within H
(a & L = b & L = 0, a != 0, b != 0),
and ANY seven independent 32-bit Magma round keys,

    D7_K((a,0),(0,b)) = 0.

The proof actually allows b=0 too, where the zero
is also implied by permutation injectivity.
There are 15*15 = 225 NONTRIVIAL H-to-H pairs.

The theorem does NOT impose any relation on keys.
Therefore it holds for EVERY legal Magma master key
and for EVERY seven-round window of the algorithm.

## Geometry of a single Magma g derivative

Delta_g(k,x,d) = g(k,x XOR d) XOR g(k,x), where

    g(k,x) = rotl11(S(x+k mod 2^32)).

All eight 4-bit S-boxes are bijections.
Addition mod 2^32 preserves the first differing input bit:
in particular, if the two input words agree on low n bits,
so do their sums with the same k.

Since only the highest input nibble can differ when d & L=0,
the first seven S-box outputs are IDENTICAL. Rotation by
11 maps the highest output S-box nibble onto bits 7..10.

The three key-universal mask consequences are:

(A) d & L=0 implies Delta_g & C=0 (high input -> band).

(B) Delta_g & C=0 implies d & L=0 (band output -> high input).
    This uses injectivity of all first seven RFC S-boxes,
    and that addition by k is invertible mod 2^28.

(C) Nonzero d & C=0 and Delta_g & L=0 cannot both hold
    (nonzero band input -> high output impossible).
    If the output is high-only, the three lowest rotated
    S-box output nibbles agree, hence so do low 12 input
    bits. But d is wholly supported in bits 7..10, so d=0,
    contradicting nonzero.

All three are statements for ALL k,x,d in the actual
32-bit Magma round function; they do NOT approximate
a carry-free S-box.

## The five-round inner contradiction

The existing proved boundary deletion gives

    D7((a,0),(0,b)) = D5_inner((0,a),(b,0)).

A genuine five-round difference trace has words

    (d0,d1,d2,d3,d4,d5,d6) =
    (0,a,p,q,t,b,0)

and five local g conditions at genuine base words x1..x5:

    Delta_g(k0,x1,a) = p
    Delta_g(k1,x2,p) = a XOR q
    Delta_g(k2,x3,q) = p XOR t
    Delta_g(k3,x4,t) = q XOR b
    Delta_g(k4,x5,b) = t.

(A) on the first and last conditions implies p,t are
supported within R. Since a!=0 and g is injective,
p != 0. Thus p XOR t is supported within R.

(B) on the central condition implies q is supported
within H. Therefore a XOR q is also H-supported.

(C) contradicts the second condition, because its
input p is NONZERO and R-supported, while the claimed
output a XOR q is H-supported.

We did NOT need to assume the five real base words were
independent; the contradiction even survives relaxing
all their correlations. No multiplication of DDTs was
performed, and all seven keys remain independent.

## Formalization and trust audit

- SevenTopNibbleImpossible.lean proves the local masks
  using RFC S-box bijectivity, real modular addition,
  inverse prefix-mask reasoning, and the actual Feistel
  base-word trajectories.
- The main theorem is named

    seven_round_high_nibble_universally_impossible

  under namespace Magma.DiffanSevenTopNibble.
- It is imported from Magma.lean. No sorry, admit, or
  user-declared axioms occur in this file.
- IMPORTANT: the Lean version's standard bv_decide
  tactic uses SAT/LRAT and proof by reflection with
  compiled checker outputs as named native axioms.
  Thus a successful lake build is NOT a pure
  kernel-only axiom-free certificate. Run #print axioms
  on the theorem and report the exact trust base.
  In particular, DO NOT claim "no axioms" merely
  because the solver reported UNSAT or lake built.
- An independent full 32-bit Z3 run with completely
  symbolic k,x,d certified each local universal
  counterexample query as UNSAT. See
  universal_seven_top_nibble.py.

## Why this does NOT yet solve nine rounds

The RFC key schedule repeats words, and the 20..28
window has the palindrome [4,5,6,7,7,6,5,4,3].
But our seven-round theorem applies to an *outer*
difference (a,0)->(0,b), while deleting nine-round
boundary rounds leaves the *opposite* 7-round slice
(0,a)->(b,0). The two cannot be identified by
reversing the keys or swapping tuples.

A separate key-independent nibble-valuation relaxation
shows the structural boundary:

    7-round outer high -> high: UNSAT.
    8-round outer high -> high: SAT relaxed stream.
    9-round outer high -> high: SAT relaxed stream.

The SAT rows are NOT real Magma witnesses. They
mean the valuation-only abstraction has exhausted
its discriminatory power after seven rounds.
Other cross-round constraints or more precise
key-linked interfaces are necessary to extend
the result to nine rounds.

Targeted tests: nibble_valuation_relaxation.py.
No broad nine-round SAT search was run.

## Further goals

First, verify the explicit native axiom dependencies
and if practical migrate the minimal bit-vector
plumbing to pure kernel proofs. Second, generalize
the mask argument to other nibble-position patterns
and characterize the maximal universal support
obstructions algebraically. Third, apply the
palindrome relation Q=G^-1 o J o G to reduce
true nine-round key-linked witness questions without
turning relaxed SAT into an all-key proof.

FROZEN: unrelated Rust aggregator formalization,
premature Rayon tuning, and bulk nine-round SAT.
