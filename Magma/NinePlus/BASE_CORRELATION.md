# Partial base-state correlation for nine-round Magma

Status: **experimental Z3 filter; not a Lean theorem of nine-round
impossibility**. This experiment separates two independent sources of
correlation: repeated RFC round keys and agreement of successive
Feistel base states.

## Exact algebra behind the filter

For an ordinary Feistel round

`G_k(L,R) = (R, L XOR g(k,R))`,

let `x_i` denote the base right-half word just before round `i`.
The right halves of an actual trajectory obey

```text
x_(i+2) = x_i XOR g(k_(i+1), x_(i+1)).
```

The XOR difference stream `d_0, ..., d_(n+1)` also obeys

```text
g(k_i, x_i XOR d_(i+1)) XOR g(k_i,x_i)
    = d_i XOR d_(i+2).
```

For a **full general** n-round slice,
`(d_0,d_1) = input difference` and
`(d_n,d_(n+1)) = output difference`.
For a nine-round **outer** slice `(a,0)->(0,s)`, the
exact two-boundary reduction yields a seven-round interior with
endpoints `(0,a)->(s,0)`.

A parameter `b` in `{0,4,8,...,32}` retains only the lowest
`b` bits of the base recurrence. Every real trajectory necessarily
satisfies every such prefix constraint.

- `b=0`: round-function g supports are coupled through the XOR
  difference words, but round base words are independent;
- `b=4,8,16`: increasingly strong, sound but not sufficient
  approximations of inter-round base-state consistency;
- `b=32`: the entire right-half base recurrence is enforced. For
  ordinary Feistel rounds, it describes actual state consistency.
  Together with common RFC master-key words and the local derivative
  equations, it is equivalent *algebraically* to a real difference
  trajectory. This equivalence has not been stated as a kernel
  theorem in Lean.

Why `b=32` is exact: `x_0,x_1` recover the original left base
half as `L_0 = x_1 XOR g(k_0,x_0)`. The recurrence then recovers
all subsequent right halves, and the local derivative constraints
ensure the second plaintext follows the same rounds. With shared
keys, a positive `b=32` model can be independently replayed
against `research/verify_nround.py`'s full RFC evaluator.

## Controlled experimental results

All experiments use RFC ordinary rounds 20..28, one symbolic master
key, the genuine 8 S-boxes, modular additions and rotations.
`--timeout-ms 600000` is a **10-minute cap per query**, not the
elapsed time. Z3 SAT models are replayed using independent Python
Magma `g`. Status `unknown` is never treated as `unsat`.

For four *general* 64-bit pairs, selected from row 2 and columns
0..3 of `fixtures/general_inputs.txt` and
`fixtures/general_outputs.txt`:

| Base bits retained | Independent-key | Linked-key | Time |
|---|---:|---:|---:|
| 0 | 4 SAT | 4 SAT | 19.14 s |
| 8 | 4 SAT | 4 SAT | 24.66 s |
| 16 | 4 SAT | 4 SAT | 38.41 s |

Each of the above 24 local SAT models was independently replayed at
the one-round derivative level. No additional impossible
differential found; increasing base correlation increased cost.
The complete reports are in `results/general_linked_600s_row2_first4.json`,
`results/general_base8_600s_row2_first4.json`, and
`results/general_base16_600s_row2_first4.json`.

For the full 8x8 **outer** difference fixture (base bits `0`),
both the independent-key and linked-key relaxation had 64/64 SAT,
190.48 seconds. This family is now design-frozen.

One positive `b=32` control uses the general input/output
`0x0000000100080000 -> 0x0000000100080000`. This is a calibration,
not a newly discovered impossibility. The linked-key Z3 model
was reconstructed into a **real RFC master key and initial state**,
then independently replayed for all nine rounds (SAT; 26.51 seconds).
See `results/general_base32_600s_control.json`.

## Reproduction

```bash
# Whole sparse outer class: 64 cells, 10 minutes available each
python3 Magma/NinePlus/local_key_coupling.py \
  --timeout-ms 600000 --limit 0 \
  --output Magma/NinePlus/results/linked_600s_all64.json

# Four general endpoints with 16-bit base recurrence
python3 Magma/NinePlus/local_key_coupling.py \
  --family general \
  --input-file Magma/NinePlus/fixtures/general_inputs.txt \
  --output-file Magma/NinePlus/fixtures/general_outputs.txt \
  --base-link-bits 16 --start-index 16 --limit 4 \
  --timeout-ms 600000 \
  --output Magma/NinePlus/results/general_base16_600s_row2_first4.json

# One exact 32-bit base-state consistency calibration
python3 Magma/NinePlus/local_key_coupling.py \
  --family general \
  --input-file Magma/NinePlus/fixtures/general_inputs.txt \
  --output-file Magma/NinePlus/fixtures/general_outputs.txt \
  --base-link-bits 32 --start-index 0 --limit 1 \
  --timeout-ms 600000 \
  --output Magma/NinePlus/results/general_base32_600s_control.json
```

The script writes an **atomic checkpoint JSON after each completed
cell**. This allows a very long run to be inspected without waiting
for every planned cell.

## Scientific decision gate

No small-prefix UNSAT has been observed yet. Therefore do **not**
bulk-formalize these SAT samples in Lean. First choose difference
classes that can force shared-carry or shared-base contradictions
(such as the already proved even/odd key clash), and measure
additional pruning versus `b=0`. If none appears after a
controlled search, freeze this branch and move to a different
family, not a larger indiscriminate SAT matrix.
