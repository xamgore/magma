# 1,908,225 key-universal seven-round impossible Magma differentials

Research status: 2026-11-04. This is a mathematically sound
**necessary-condition obstruction** for the true RFC 8891 g
round function, checked by full symbolic Z3 with ALL 32-bit
key/base words free. Six disjoint nibble-index classes
exclude 1,908,225 nonzero (a,b) boundary pairs for EVERY
seven-round key sequence.

The 225 high/high subfamily has additionally been
formalized as a full seven-round DDT equality theorem in
Magma/Diffan/SevenTopNibbleImpossible.lean. The other
1,908,000 pairs have NOT yet received individual Lean
theorems; do not call the whole million-plus family
kernel-certified.

## Universal single-round invariant

Represent a nonzero 32-bit word d as eight 4-bit nibbles
numbered 0..7 from least to most significant. Let

    nu(d) = MIN{i : nibble_i(d) != 0}.

Then for ALL 32-bit key k, concrete base x, nonzero
XOR input difference d and g derivative

    e = g(k,x XOR d) XOR g(k,x),

the following key-independent equality holds:

    nu(rotateRight(e,11)) = nu(d).

Reason: if two input words first differ at bit m,
adding the same k modulo 2^32 preserves their equality
modulo 2^m, and preserves their difference modulo
2^(m+1). In particular, the first changed nibble of
x+k and (x XOR d)+k is identical to the first changed
nibble of x and x XOR d. Each RFC S-box is bijective,
so the first changed S-box-output nibble is the same.
The rotation is explicitly undone.

Conversely d=0 forces e=0, and g's bijectivity means
a nonzero d cannot give zero e. The abstraction used
below thus sets a pair (d,e) possible exactly when
both are zero, or both have nonzero matching nu after
undoing rotate-left-11.

This is only a NECESSARY differential relation, not
a characterization of all S-box/carry weights.
It allows the five rounds to choose keys and bases
independently; that makes any UNSAT especially strong.

## Genuine seven-to-five boundary deletion

For any independent seven keys K,

    D7_K((a,0),(0,b)) =
       D5_inner((0,a),(b,0)).

Any real five-round Feistel trace on the RHS has
difference stream

    (d0,d1,d2,d3,d4,d5,d6)=(0,a,p,q,t,b,0)

and, at each of its five local derivatives,

    nu(rotateRight(d_i XOR d_(i+2),11))
       = nu(d_(i+1))

unless BOTH the derivative's input and output are zero.
Every real Magma trace must satisfy this constraint,
even if the master key repeats words.

A symbolic Z3 query tests whether *any* difference-only
stream obeys all five necessary relations. The input
and output a,b are themselves symbolic with prescribed
first-active nibble indices i,j, respectively. HIGHER
input/output nibbles are entirely free: the query
does not assume a or b is one-hot or one-nibble-only.

## Exhaustive 8 x 8 nibble-index classification of this filter

Columns represent nu(b)=0..7; rows nu(a)=0..7.
X means UNSAT (proof of universal real D7 zero).
. means SAT for the RELAXATION ONLY; it is NOT a
genuine Magma differential witness.

    nu(a)       nu(b) 01234567
       0              ........
       1              ........
       2              ........
       3              ........
       4              ........
       5              ......X.
       6              .....XXX
       7              ......XX

Exactly six disjoint position families are rejected:

| nu(a) | nu(b) | Distinct (a,b) pairs |
|---:|---:|---:|
| 5 | 6 | 921,600 |
| 6 | 5 | 921,600 |
| 6 | 6 | 57,600 |
| 6 | 7 | 3,600 |
| 7 | 6 | 3,600 |
| 7 | 7 | 225 |
| **Total** | | **1,908,225** |

For nibble index i, the number of 32-bit nonzero words
with nu(d)=i is precisely 15*16^(7-i): the lower i
nibbles vanish, nibble i is nonzero (15 choices),
and all 7-i more significant nibbles are arbitrary.
The six index classes are disjoint, so the total
counts 1,908,225 DISTINCT nonzero endpoints.

These exclusions hold for ALL seven independent round
keys and therefore for every actual Magma master key
and every seven-round window.

## Two independent Z3 layers and their trust boundary

A. The --check-real-g option constructs the ACTUAL
RFC 8891 g in Z3 with fully free 32-bit key, base
and XOR difference. For all eight possible nu(d),
it asks for a violation of the valuation rule.
All eight negated local properties are UNSAT,
each in about 2-3 milliseconds on the tested Mac.

B. The main 8x8 scan uses only differences, never
mentions g or master keys, and asserts the necessary
five-step valuation relation. All 64 status checks
completed in under a second; exactly six families
were UNSAT. Endpoints are free 32-bit words restricted
by their FIRST active nibble, not chosen examples.
The arithmetic and counting formula is independent
of solver correctness.

The actual Magma applicability follows from the
mathematical preservation of first differing nibble
above, even without trusting a single fixed-key
count. Z3 reproducibility is computational evidence;
UNSAT is not an axiom-free Lean proof certificate.

## Formal subfamily and explicit axiom audit

The existing
Magma/Diffan/SevenTopNibbleImpossible.lean theorem

    seven_round_high_nibble_universally_impossible

has arbitrary Fin 7 -> BitVec 32 keys. It proves D7=0
for all nonzero a supported only in bits 28..31 and
any b supported there. This covers exactly the
225 nontrivial (nu(a),nu(b))=(7,7) word pairs.

Both Feistel trajectories are represented exactly
in Lean. The proof uses modular addition,
bijective RFC S-boxes and the already proved
boundary deletion. No sorry/admit is used.

CAUTION: the Lean 4 version's standard bv_decide
tactic produces named native proof-reflection axioms
from a compiled LRAT-checking path. The exact
#print axioms output for this theorem has the
standard propext, Classical.choice, Quot.sound, and
40 **local** _native.bv_decide.ax_* declarations.
There are NO inherited AutomaticOutputMasks native
axioms after replacing the generic mask lemma
with a self-contained proof.

Thus this Lean build is SAT/LRAT-backed and
elaborated, but not a proof with only the bare
Lean kernel in the trusted base. A fully
axiom-free bitvector-plumbing translation remains
a distinct formal-strengthening task and should
not be confused with the mathematical claim.

## Precise seven-/eight-/nine-round scope

The DIFFERENCE-only valuation abstraction rejects
nu(a)=7,nu(b)=7 for a FIVE-round inner core (SEVEN
outer rounds). For six-/seven-round inner cores
(EIGHT/NINE outer rounds), that same H-to-H
abstraction has a satisfiable relaxed trace.

In fact, the 8x8 scan with representative one-nibble
endpoints found NO excluded position families at
either eight or nine outer rounds under this
weak valuation rule. SAT here only identifies
a barrier for the relaxation: it does NOT prove
actual eight/nine-round support.

An all-key 9-round impossible differential, if one
exists, needs a stronger invariant: cross-nibble
S-box support, linked key conditions, or correlated
base-state constraints. The bulk nine-round SAT
freeze is unchanged.

## Reproduce

    python3 Magma/Composition/nibble_universal_family_scan.py --check-real-g
    python3 Magma/Composition/universal_seven_top_nibble.py
    python3 Magma/Composition/nibble_valuation_relaxation.py
    lake build Magma.Diffan.SevenTopNibbleImpossible
    lake build Magma

For trust-base inspection:

    printf 'import Magma.Diffan.SevenTopNibbleImpossible\n#print axioms Magma.DiffanSevenTopNibble.seven_round_high_nibble_universally_impossible\n' >/tmp/CheckSeven.lean
    lake env lean /tmp/CheckSeven.lean

DO NOT promote relaxed SAT examples to real Feistel
witnesses or convert UNKNOWN/LIMIT into a zero.
