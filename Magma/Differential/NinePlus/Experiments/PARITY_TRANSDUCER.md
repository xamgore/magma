# One-bit shared-key transducer for Magma difference streams

Status: **experimental fast filter backed by kernel-proved one-round
support lemmas**; no new 9-round impossible differential established.

## Mathematical source and scope

RFC Magma's exact one-round XOR-DDT row at input difference `1` has
been proved in Lean in these core files:

- `Magma/DDT/ZeroLeft/EightEntries.lean`: exactly 8 possible
  output differences for an **even** key word;
- `Magma/DDT/UnitInput/Odd77.lean`: exactly 77 for an **odd** key;
- `Magma/DDT/ZeroLeft/ParityCompleteSlice.lean`: the row for
  any 32-bit round key depends **only on its parity**;
- `Magma/Differential/NinePlus/ParityCollision.lean`:
  `same_key_pair_parity_necessary`, a kernel-checked lemma that
  TWO actual unit-input g derivatives using a shared key must admit
  one common key parity.

The even/odd output sets overlap at precisely three post-rotation
differences: `0x00001000`, `0x00004000`, `0x00007000`.
The Python script checks these sets against their exact Lean source
tables, with SHA-256 hashes of those source files.

Consequently, for two occurrences of **input difference 1** with the
same master-key word:

| Count of pairs of distinct output-mask *choices* | Number |
|---|---:|
| Each round uses its own key parity | 82² = 6,724 |
| Both use one shared key parity | 8² + 77² - 3² = 5,984 |
| Eliminated strictly by key reuse | **740 (11.00535%)** |

This counts **ordered pairs of supported output masks**, NOT
probability mass, and makes no claim about the rate among arbitrary
intermediate difference streams. The filter has no information
when the local g-input difference is not exactly `1`.

## O(rounds) parity-word filter

`parity_transducer.py` maintains one 2-bit *allowed-parities mask*
for each of the eight 32-bit RFC master-key words. For every ordinary
round `i`, let the difference stream be `d_i, d_(i+1), d_(i+2)`.
When `d_(i+1)=1`, compute its required g-output difference

    e_i = d_i XOR d_(i+2).

If `e_i` is in the even-key reference support, permit parity 0;
if it is in the odd-key support, permit parity 1; take both if
the sets overlap. Intersect the mask into the variable corresponding
to the RFC `key_index(start+i)`. A zero mask refutes that **specific
word-difference stream** under every master key.

Otherwise the filter says only **not excluded**. In particular,
the algorithm DOES NOT assert that the stream satisfies the true
g-differences at input words other than 1, that base states are
correlated, or that fixed endpoints cannot follow some other stream.
A real RFC trajectory cannot be falsely rejected by this rule
assuming the exact Lean reference supports.

Computational complexity is O(number of rounds), with O(8) memory.
All 85 reference-set entries are cached in Python sets; the helper
can also export a JSON lookup for a future Rust carryDP implementation.

## Reproducible checks

From the repo root:

```bash
python3 Magma/Differential/NinePlus/Experiments/parity_transducer.py \
  --motif-report Magma/Differential/NinePlus/Experiments/results/full9_parity_w4.json \
  --output Magma/Differential/NinePlus/Experiments/results/full9_w4_parity_filter.json

python3 Magma/Differential/NinePlus/Experiments/parity_transducer.py \
  --sat-run Magma/Differential/NinePlus/Experiments/results/sat_runs/round9_window0_sparse8 \
  --max-sat-witnesses 64 \
  --output Magma/Differential/NinePlus/Experiments/results/real_rfc_parity_filter_64.json
```

First check: **rejected** forced inner route for RFC rounds
23 and 24, where both use `k7` but require even and odd parity.
Second check: **all 64 genuine RFC nine-round positive witnesses
accepted**. Of them 16 contain unit-input local derivatives, 17
such occurrences total; the remaining witnesses naturally exercise
only the filter's pass-through behavior.

## A nine-round forced-route experiment (NOT an endpoint ID)

`full9_parity_motif.py` tests the full nine-round difference stream

    [0, A, B, 0x1801, 1, 1, 0x2801, U, S, 0, S]

for the window at RFC rounds 20..28. Endpoints are `(0,A)->(0,S)`.
The adjacent uses of `k7` at rounds 23 and 24 are required to
realize one-round differences `1->0x1800` (even-only) and
`1->0x2800` (odd-only). Hence no key-linked route of THIS form.

- If A,S each have at most 1 or at most 2 bits set, even independent
  keys yield UNSAT for this **forced inner route** (Z3).
- At most 4 bits each: independent-key model SAT (full local witness
  independently replayed), key-linked model UNSAT.
- One independent witness has A=`0x00102402`, S=`0x0080080a`,
  exactly four set bits in each word. This is a **test candidate only**.
- Removing the forced middle differences, the genuine local
  key-linked support relaxation is SAT even at 0, 8 and 16
  bits of base-state correlation. This confirms that alternate
  internal routes remain possible.

The separate seven-round `parity_motif_search.py` shows the
same distinction in the inner window; putting BOTH outer boundary
halves to zero makes the chosen motifs impossible even when keys
are independent. **None of these results is a 9+ impossible
differential of the observable encryption function.**

The 7-round complete RFC SAT on two pairs at window21 produced
four UNKNOWN at 60 s. A separate Z3 test at 600 s for one
7-round boundary gave independent-support SAT and key-linked
full-base UNKNOWN. Timeouts are not impossibility evidence.

## Research stop rule

Use this transducer as a **cheap path-pruning oracle** inside a
longer-round truncated/carry-DP state enumeration. Quantify new
paths removed relative to the existing local support checker and
compare final endpoint reachability. Only then invest in a
large Lean formalization or a Rust-optimized implementation.
Without an endpoint class that forces the invalid route, freeze
expansion of the concrete motif family.
