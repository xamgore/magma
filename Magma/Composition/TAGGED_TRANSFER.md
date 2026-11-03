# Tagged Magma carry steps → exact triple-fiber transfer research

Status: 2026-11-03. Core Lean whole-word reconstruction **PROVED**;
local full-width triple factor and a toy exact weighted transfer **TESTED**;
full-width compressed five-round DDT transfer **NOT YET IMPLEMENTED**.

## 1. Reusable kernel-checked one-round lemma

`TaggedCarryWord.lean` builds on the existing
`GBaseTaggedCarryStep.lean` and `Carry/Automaton.lean`.
Given arbitrary Magma key `k`, base word `x` and XOR input
difference `d`, `taggedPrefix` actually **executes eight
successive** `taggedCarryStep` transitions, passing the resulting
pair of carries to the next nibble. Its stepwise invariant is
`taggedPrefix_correct`.

`taggedPrefix_eight_g` proves from that executable trace:

```text
rotateLeft11(pack(baseTags)) = g(k,x)
rotateLeft11(pack(diffTags)) = g(k,x XOR d) XOR g(k,x)
```

The corresponding pre-rotation statements are in
`taggedPrefix_eight_words`. Additional useful building blocks:
`actualTagged_next_carries`,
`actualTagged_diff_word_digit`, `pack_actualTagged_difference`.
These are general lemmas (for every 32-bit key/base/difference),
not individual `decide` witness certificates. No `sorry`
or new `axiom`.

Run: `lake build Magma.Composition.TaggedCarryWord`.
The core theorem is imported by `Magma.lean`.

## 2. Actual three-chain correlation, one nibble at a time

`triple_carry_nibble_probe.py` implements a local three-trace
factor for the existing five-round inverse join, reparameterized
by the middle input `z`:

```text
c = gDiff(k1, r, a)
gDiff(k2, z, c) = a XOR b
gDiff(k3, r XOR g(k2,z), b) = c
```

At nibble `i`, the first chain emits a pre-rotation derivative
tag `E_i`; the middle chain emits its BASE substitution tag
`U_i`; the third chain consumes the actual base nibble
`r_i XOR (rotateLeft11(U))_i`.

For RFC rotate-left-11, the output nibble `i` depends on
**exactly the previous two delayed tag positions**:

```text
(rot11(tags))_i =
    (tags[(i-3) mod 8] >> 1)
  | ((tags[(i-2) mod 8] & 1) << 3)
```

The factors are genuinely local once incoming carry pairs and
the necessary delayed tags are specified; each nibble enumerates
16×16 assignments of the two base digits `r_i,z_i`.
Three independent carry pairs contribute six bits.
A straightforward streaming buffer can require up to
11 delayed bits per tag stream (22 together), giving a
**naive 28-bit interface estimate**, BEFORE optimization and
cyclic-boundary bookkeeping. This is not a proven minimal
state size, nor an observed full-width DP frontier.

The reference script checked 512 deterministic full RFC Magma
`g` triples and 32 sampled local transfer rows. It also
recovered and accepted exact nonzero triples from the existing
kernel-certified witnesses:

- 1-hot → 4-hot, `a=0x00000080, b=0xc0000820`,
  recorded in `OneHotFourHotPositive.lean`;
- 2-hot → 3-hot, `a=0x80000080, b=0x20200020`,
  recorded in `SparsePositiveWitnesses.lean`.

Each of the eight actual nibble factors accepts both witnesses.
These are **real full-width Magma regression checks**, but NOT a
calculation of the total five-round DDT.

Run: `python3 Magma/Composition/triple_carry_nibble_probe.py`.
Report: `tagged_triple_probe.json`.

## 3. Exact weighted transfer-DP on a completely enumerable toy

`toy_triple_exact_regression.py` uses the first two genuine RFC
S-boxes, **8-bit** modular addition, and rotate-left-3.
It is a reduced toy cipher, **NOT full-width RFC 8891**.

The transfer state contains the six real carry bits and six
delayed S-box tag bits, totaling 12 bits. Initial cyclic
boundary tags are guessed (64 possibilities), and closure is
enforced after nibble 1. For each state/nibble, the transfer
enumerates the 16×16 base-digit pairs, retains only accepted
three-chain constraints, and **sums multiplicities**. Final
carry states are unrestricted (modulo 2^8).

Against the independent, direct 2^16-state five-round Feistel
DDT and the exact 2^8×2^8 triple fiber enumeration:

| Toy case | Direct 5-round DDT | Triple join | Weighted DP | Naive independent-DDT convolution |
|---|---:|---:|---:|---:|
| zero input/output | 65,536 | 65,536 | 65,536 | 65,536 |
| `a=0x87, b=0x3f` | **12** | **12** | **12** | **656** |
| `a=0x87, b=0x00` | **0** | **0** | **0** | **40** |

The nonzero positive case exhibits a **coupling defect of 644**;
the nonzero-input impossible case exhibits a **defect of 40**,
with the same fixed five toy round keys. Both defects represent
false paths introduced by naive marginal-DDT multiplication. The
weighted transfer agrees exactly; naive DDT multiplication
overcounts. Its maximum observed frontier width in this test
was **8 states** (toy only). The zero case saw width 44.
All values are verified by independent Python computations;
they are not Lean-certified toy theorems.

Run: `python3 Magma/Composition/toy_triple_exact_regression.py`.
Report: `toy_triple_exact_regression.json`.

## 4. What is still missing

**Next P0 obligation:** formalize the rotate-left-11 nibble
mixing identity above in Lean and give the same exact cyclic
boundary-closure implementation for **eight** nibbles.
The first direct `bv_decide` attempt did not preprocess
the custom digit/Nat operations into supported BitVec terms;
no unproved theorem was added as a workaround.

**Next experimental gate:** measure the maximum frontier
width and runtime on real 32-bit key/difference fixtures.
The naive 28-bit interface is only a design upper estimate;
a practical algorithm might require better elimination
ordering or a different factorization. A first large DP
that still enumerates all 2^64 `(r,z)` values would not
be a successful optimization.

**Then P1/P2:** prove that the weighted full-width contraction
equals `fiveRound_eq_three_carry_traces`, and regress it
against established true/false fibers and strict joining
defects before attempting any 7/9+ round composition.

The nine-round SAT/motif branch remains frozen:
`Magma/NinePlus/DESIGN_FREEZE.md`.
