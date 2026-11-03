# Can RFC 8891 Magma have a key-independent impossible differential beyond 8 rounds?

Research checkpoint: 2026-11-03. **Status: open, no 9+-round ID found.**

## Quantifiers and literature: do not mix different questions

A universal (key-independent) impossible differential of n ordinary
Magma Feistel rounds is a pair of distinct nonzero 64-bit differences
(alpha,beta) for which **for every RFC master key K and base X**,
the n-round XOR derivative never equals beta. A solver SAT cell only
shows **some K and some X** realize it. Solver UNSAT after faithfully
modeling the full key schedule is evidence of the universal exclusion;
a Lean certificate would be stronger.

- Ishchukova, Pismensky, Babenko (2016): 8-round impossible
  characteristics for **Magma+**, and longer rounds as future work.
  The paper does *not* establish that 9+-round IDs in RFC Magma
  are impossible. Source:
  https://s.top-technologies.ru/pdf/2016/2016_12_3.pdf
- RFC 8891: exact standard S-box, ordinary round G, last G*,
  256-bit master schedule. Source:
  https://www.rfc-editor.org/rfc/rfc8891.html
- Hu et al., *Revisit the Propagation of States* (IEEE TIT 2026):
  existing key-schedule-aware ID searches and state-propagation
  models. Do not claim to have originated the whole idea of
  state-aware impossible-differential automation.
  DOI: https://doi.org/10.1109/TIT.2025.3627983
- Dinur, Dunkelman, Shamir et al. and *Cryptanalysis of GOST2*
  already discuss reflection-style attacks on GOST variants.
  https://cris.haifa.ac.il/en/publications/cryptanalysis-of-gost2/

Avalanche behavior does not logically prove there are no
key-independent zero DDT cells. Conversely, no evidence of 9+
ID in a small search does not prove nonexistence.

## Existing exact baseline

For the outer class (a,0) -> (0,s) at ordinary rounds 0..8,
all 32x32 **one-hot -> one-hot** pairs are SAT, and each of the
1024 positive master-key/base witnesses has been checked by Lean.
The theorem states an existential master key **per pair**,
not a common key for all pairs. This does not cover other
input/output difference classes.

## New controlled nine-round scan: two key-schedule positions

Define eight full-word differences, in both input left half
and output right half, with the other halves zero:

    0x00000001  0x00100000  0x01000000  0x10000000
    0x10000001  0x10100000  0x81000000  0x90000000

The first four are one-hot; the last four are two-hot.
The matrix has 8x8 = 64 cells, one symbolic RFC master key per
SAT query, eight parallel workers and a 5000-ms cell timeout.

| Ordinary round window | SAT | UNSAT | TIMEOUT | SAT elapsed |
|---|---:|---:|---:|---:|
| 0..8 | 64 | 0 | 0 | 8.4 s |
| 20..28 | 41 | 0 | 23 | 32.5 s |

For four initially timed-out cells from the second window, re-run
the 2x2 subset {0x1, 0x10000001} both as inputs and outputs with
a 25000-ms per-cell timeout: **4 SAT, 0 UNSAT, 0 TIMEOUT**,
20.8 s for all four. The difference between schedules so far
shows **solver difficulty**, not a new impossible differential.

All 64+41+4 positive witnesses were independently replayed by
`research/verify_nround.py`, and compressed matrix SHA-256
checks matched metadata. Raw runs live in ignored directories:

    research/nround_runs/round9_window0_sparse8/
    research/nround_runs/round9_window20_sparse8/
    research/nround_runs/round9_window20_hard4_25s/

Fixtures live alongside this note and can be rerun using
`research/magma_exact_matrix_nround.rs -- --family outer`.
Always include `--rounds 9` and the desired `--window-start`.

## A structural reason to inspect the schedule boundary

At ordinary rounds **20..27**, RFC subkey indices are:

    [4, 5, 6, 7, 7, 6, 5, 4]

This is palindromic. For any Feistel G_k and half-word swap J,

    G_k^-1 = J ∘ G_k ∘ J.

Let H be the first four rounds, E8 the full palindrome
and Q := J ∘ E8. Then

    Q = H^-1 ∘ J ∘ H,       Q² = id.

Consequently Q has **exactly 2^32 fixed states for every master
key**, the preimages under H of all (z,z) states. This is pure
Feistel algebra and not specific to Magma S-boxes. A reproducible
Python test, `reflection_window20.py`, checked the identity and
constructed fixed states for 2400 random trials; **the fixed-point
count follows algebraically**, not statistically.

Nine rounds 20..28 append another round after this symmetric
8-round core. Correlations of repeated subkeys may provide a
new filter for 9+ impossibility, but the reflection identity
by itself implies NO forbidden difference cell. Reflection
attacks on GOST have substantial prior art.

## What would justify a new heavy Lean proof?

Use a staged, falsifiable approach, not another giant witness table:

1. Try *general* 64-bit differences with both halves active,
   deliberately placed high/low nibbles, and boundary windows
   with a reflected key schedule. Do not just revisit 9-round
   one-hot -> one-hot: that full class is already positively settled.
2. Compare constraints in a strict hierarchy:
   (a) independent genuine Magma g-support carryDP per round,
   (b) shared key-nibble variables at schedule collisions while
       retaining independent per-round base words,
   (c) full correlated bases and master-key schedule in SAT.
   Report pruning beyond (a) and (b), **not only execution time**.
3. Regard SAT as existence and 5/25-second timeouts as UNKNOWN;
   increase timeouts only for a small nominated set of promising
   cells, and replay every positive model independently.
4. Only if (b) or (c) proves a 9+-round UNSAT family, derive a
   compact Lean-checkable certificate and an explicit use in an
   even longer multi-round cut. Otherwise archive the negative
   finding and move to different truncated/general classes.

A 9+-round zero with the quantifiers over **all** RFC keys is the
milestone. No such claim is established by the experiments above.
