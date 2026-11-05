# Opposite five-round core, exact seven-round checks, general three-round transfer

Status: 2026-11-03. **Executable and independently verified** with
real RFC 8891 S-boxes, 32-bit modular carries and fixed round keys.
No new 9-round impossible differential. No Rust aggregation proof
in Lean; previous full-transfer proof freeze remains in force.

## Why the orientation matters

The existing kernel theorem in
Magma/Differential/Windows/FirstRoundDeletion.lean proves, for fixed round keys:

    D7[(a,0) -> (0,b)] = D5_inner[(0,a) -> (b,0)].

Our older exact five-round outer transfer only covered
D5[(a,0)->(0,b)]. It cannot simply be substituted into the
oppositely oriented 5-round inner problem. Nor does a key-free
path-reversal lemma imply a fixed-key DDT reversal.

## Exact five-round fiber in two 32-bit base words

For ordinary Feistel rounds with keys k0..k4, let x0,x1 be
the two starting BASE words, and

    x_(i+2) = x_i XOR g(ki,x_(i+1)).

Take r=x2 and z=x3. This is a bijective reparameterization
of the entire 64-bit plaintext base space because

    x1 = z XOR g(k1,r)
    x0 = r XOR g(k0,x1)
    x4 = r XOR g(k2,z)
    x5 = z XOR g(k3,x4).

For input difference (0,a), let d0=0,d1=a and let the
right-word XOR difference stream be

    (d0,d1,d2,d3,d4,d5,d6) = (0,a,p,q,t,b,0).

With gDelta(k,d,x)=g(k,x XOR d) XOR g(k,x), five **real**
derivative equations are

    gDelta(k0,a,x1) = p
    gDelta(k1,p,r)  = a XOR q
    gDelta(k2,q,z)  = p XOR t
    gDelta(k3,t,x4) = q XOR b
    gDelta(k4,b,x5) = t.

The total exact fixed-key fiber count is the cardinality
of (r,z) satisfying the resulting two final word equations.
opposite_five_fiber.py implements both this equation system
and a DIFFERENT direct symbolic five-round Feistel encoding,
enumerating and blocking full 64-bit base models.
verify_seven_direct.py independently builds a true
seven-round symbolic Feistel circuit without using 7->5,
and independently replays every model against
Magma/Differential/Windows/Experiments/SAT/verify_nround.py. All three models compare the
SHA-256 of the SAME sorted middle-base pair set. They
must all complete to UNSAT for an exact count.

## Fixed keys and exact seven-round results

Master key words for ordinary RFC rounds 0..6 are

    [0x12345678, 0x00000000, 0x00002056, 0xfdfa7789,
     0xf0f8d960, 0x00000000, 0x87654321]

(the eighth master word, not used by the seven rounds,
may be 0xdeadbeef). Interior five-round keys are words
1..5 from this master schedule.

| Seven-round input (a,0), output (0,b) | Exact D7 | Proof by computation |
|---|---:|---|
| a=0x80000000, b=0x681e60a7 | **2** | all THREE independent SMT encodings enumerate the same two pairs and exhaust to UNSAT |
| a=0x00000001, b=0x00000001 | **0** | all THREE encodings UNSAT |
| a=0x80000000, b=0x681e60a6 | **0** | all THREE encodings UNSAT |

All positive solutions are checked against the real seven-round
RFC Feistel encryption. Changing the first and last seven-round
keys while keeping all five inner keys fixed preserves the
count **2** and the exact middle-base pair set; this agrees
with the already proved boundary-key-independence theorem.

**These three specific controls remain fixed-key DDT
results, NOT universal zero claims.** The zero control
outputs 0x00000001 and 0x681e60a6 are not justified for
all master keys by these numerical checks.

**Separate 2026-11-04 breakthrough:** the key-universal
high/high seven-round family has now been proved as an
actual D7=0 Lean theorem with arbitrary seven-round keys;
this includes all 225 nontrivial highest-nibble endpoints.
A stronger algebraic *necessary valuation* obstruction,
verified against full symbolic Magma g and 64 symbolic
five-chain nibble-index cases, excludes 1,908,225 distinct
seven-round endpoint pairs in six disjoint position classes.
See [NIBBLE_VALUATION_FAMILIES.md](NIBBLE_VALUATION_FAMILIES.md).
The 225-pair subfamily has been formalized in Lean; the
other classes are mathematical/Z3 results, not individual
Lean theorems. Lean bv_decide uses compiled LRAT-check
native axioms; the exact trust audit is in that document.
None of this implies a nine-round impossibility.

## General three-round g/carry composition (new)

Any REAL central three rounds with key words k1,k2,k3,
input difference (A,P), output difference (T,B), and
intermediate right differences Q, has

    e_first  = A XOR Q
    e_middle = P XOR T
    e_last   = Q XOR B = e_first XOR A XOR B.

Therefore, writing E for the first g derivative S-box
tag stream BEFORE rotate-left-11:

    Q = A XOR rot11(E),
    middle input difference = Q,
    middle derivative output = P XOR T,
    third derivative output tags
      = E XOR ror11(A XOR B).

The middle BASE g output h is shared with the third
derivative's BASE input: its base is r XOR h.
The exact middle S-box tags, all six real carry bits
and both delayed cyclic tag streams are still coupled.
This changes only the local constraints of our existing
joint_middle_transfer.rs. No new independence assumption
has been introduced.

**General 3-round CLI:**

    rustc -O -C target-cpu=native \
      Magma/Differential/FiveRounds/Experiments/joint_middle_transfer.rs \
      -o /tmp/magma_joint_three

    /tmp/magma_joint_three \
      --keys 0x2056,0xfdfa7789,0xf0f8d960 \
      --core-input-left 0x12345678 \
      --alpha 0x9abcde12 \
      --beta 0x216ed12f \
      --core-output-right 0x3f6e53d2 \
      --free-bits 32 --max-seconds 60 \
      --max-edges 2000000000 --max-frontier 250000

For historical compatibility, --alpha is the input RIGHT
word P and --beta is the output LEFT word T. Both new
flags default to zero, reproducing the old D5 outer
calculation via the established exact D5->D3 boundary
reduction. All 15 old regression counts were rerun and
passed, including full 768 and 30,720.

| Exact general 3-round fixed-key DDT | Rust carryDP | Independent Z3 | Measured Rust time |
|---|---:|---:|---:|
| (0x12345678,0x9abcde12) -> (0x216ed12f,0x3f6e53d2) | **48** | **48**, exhausted to UNSAT | ~0.60–0.87s |
| (0x80000000,0x00000580) -> (0xa7018a3d,0x681e60a6) | **0** | **0**, UNSAT | ~1.04s |

verify_joint_three.py independently solves the entire
three-round Feistel circuit with two free 32-bit original
base words, and replays all positive models with RFC g.
It does not import the Rust transfer's internal equations.

## Strict improvement beyond independent one-round DDT

For the *third seven-round test above*, the five
**independent** one-round g derivatives are all individually
satisfiable under the SAME fixed k0..k4. The exact
difference stream of one local-support witness is

    (0,0x80000000,0x00000580,0x5be38006,
     0xa7018a3d,0x681e60a6,0).

Nevertheless, the ordinary Feistel middle-base relation

    x4 = x2 XOR g(k2,x3)

makes the local five-derivative model **UNSAT**,
even WITHOUT linking the first/last round base words
x1 and x5 to the central three-round bases.
Restoring these other two base equalities also remains UNSAT.
The independent *whole* seven-round solver is UNSAT.

This is a reusable **necessary three-round support filter**:

    D5[(0,a)->(b,0)] > 0
      IMPLIES some p in support(gDelta(k0,a,_)),
                   t in support(gDelta(k4,b,_))
      have D3[k1,k2,k3]((a,p),(t,b)) > 0.

The converse is generally FALSE because a central three-round
witness may fail the outer base-state consistency equations.
For the strict fixed-key example, no candidate (p,t)
survives the central real three-round coupling.
We measured this by a single Z3 query over all possible
p,t; the displayed 3-round zero is one *illustrative*
candidate, not a claim that checking just one candidate
proves the entire seven-round zero.

## Reproduce the whole package

    python3 Magma/Differential/SevenRounds/Experiments/seven_core_regression.py

The 10- to 15-second regression checks:
- three independent completed SMT counts for each of three
  real seven-round endpoints, including identical pair-set hashes;
- different first/last round keys still give the same two solutions;
- independent g-support SAT versus middle-base coupling UNSAT;
- general three-round Rust full weighted counts 48 and 0
  versus complete independent three-round SMT;
- input/output g functions are replayed independently.

Existing old five-round regression:

    python3 Magma/Differential/FiveRounds/Experiments/joint_middle_regression.py --full
    lake build Magma

JSON fixtures in this directory preserve exact statuses and
model hashes; UNKNOWN/LIMIT is never recorded as UNSAT.

## Next gate: actual seven-/nine-round compositional algorithm

**Second 2026-11-04 update:** [OVERLAPPING_J.md](../../Reflection/Experiments/OVERLAPPING_J.md)
derives the exact two-overlapping-three-round (5=3+3-1) conditional
J identity. Its real 32-bit Magma SMT implementation matches the
same exact counts 2,0,0,8 and sorted middle-base solution hashes.
This is NOT scalar-J DDT multiplication: on a one-nibble toy that
naive factorization falsely accepts all 136 actual zero endpoints.
An exact 24-bit-interface ROBDD toy join reproduces 225/225 DDTs,
but direct BDD circuit construction still hits LIMIT at 8-bit-word
scale. The next target is nibble-local conditional-J composition,
not a bulk 9-round SAT search or redundant formal Rust proof.

**2026-11-04 update:** [FIVE_FACTOR_PROBE.md](../../FiveRounds/Experiments/FIVE_FACTOR_PROBE.md)
adds a real five-g dual-carry/tag local encoding, independent SMT
cross-checks for completed 2,0,0,8 fiber counts, and graph-width
analysis of a full correlated join. This closes the *factor-graph
semantics/structural-width experiment*, but not the seven-round
DP goal. A first true integer-weight sparse join now completes ten
one-nibble toy tests; the real 32-bit problem reaches an explicit
LIMIT even at one million factor rows (173/307 variables eliminated).
The naive dense factor width is far too large, and simple sparse
joining does not resolve it: a compressed symbolic elimination is
still needed. Reproduce with `../../FiveRounds/Experiments/five_factor_gate.py` and
`../../FiveRounds/Experiments/five_factor_sparse_regression.py`.

Phase 1 of ROADMAP.md has now achieved exact numeric
fixed-key seven-round controls and the correct five-core
fiber formula; a **fast full five-core carryDP is NOT
yet implemented**. Phase 2 has a genuinely general
three-round weighted block, but joining it with BOTH
outer g-derivative constraints while preserving their
real base words is still open.

The immediate algorithmic task is to extend the shared
tag/carry factor graph with the two outer g constraints,
not multiply their marginal DDTs. Measure frontier size
and progress against both positive and strict-zero seven
controls; preserve full RFC master-key coupling when later
transitioning to nine rounds. No broad nine-round SAT
campaign or unneeded Rust formalization.
