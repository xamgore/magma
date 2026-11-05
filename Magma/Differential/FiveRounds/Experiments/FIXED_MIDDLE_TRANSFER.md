# Full-width fixed-middle Magma carry transfer

**Research status (2026-11-03):** The exact local 11-bit-closure
counting algorithm is implemented and computationally cross-checked
against independent Z3 enumeration. Its one-round semantics and
rotate-left-11 digit wiring are kernel-proved in Lean. The **weighted
DP ↔ full fiber bijection itself has NOT yet been formalized in Lean**.
This fixed-h script does not sum over all h. The later
joint-middle transfer now computes the complete fixed-key
five-round counts; see JOINT_MIDDLE_TRANSFER.md.

## The exact conditional fiber

For fixed 32-bit keys k1,k2,k3, outer input a and output b, and a
fixed 32-bit middle **base** h, define z := g_k2^-1(h); the inverse
exists because key addition, each RFC S-box, and rotate-left-11 are
bijections. Then count the 32-bit base values r such that

    c = g_k1(r XOR a) XOR g_k1(r)
    g_k2(z XOR c) XOR g_k2(z) = a XOR b
    g_k3((r XOR h) XOR b) XOR g_k3(r XOR h) = c.

This is a fixed-h slice of the exact three-trace formulation already
proved in Magma/Differential/ThreeRounds/ThreeCarryTraceJoin.lean, under the outer
five-round boundary identity. In particular, it retains **all
correlations of r between the first and third derivatives** and the
middle base h. It does not multiply independent round DDTs.

## Eight-nibble weighted transfer

Executable: fixed_middle_transfer.py.

1. Fix h and invert g_k2 to obtain the unique z. Therefore the
   complete second-chain BASE S-box tag word U is already known.
2. Introduce eight unknown first-chain S-box derivative digits
   E0..E7 and true running carry pairs for the three g derivatives:
   **six carry bits** before each digit.
3. The true rotate-left-11 nibble wiring is:

       c_i = (E_(i-3) >> 1) | ((E_(i-2) & 1) << 3)
       h_i = (U_(i-3) >> 1) | ((U_(i-2) & 1) << 3),

   with indices modulo 8. The h_i are already fixed.
4. Guess only E5 high three bits, E6 all four bits and E7 all four
   bits: **11 initial cyclic boundary bits = 2048 possibilities**.
   No guess of E5's low bit is necessary; it is emitted before use.
5. Each digit enumerates the 16 possible r_i values. The *same*
   r_i feeds the first and third derivative, while second-chain
   input difference comes from the delayed E tags. Reject any digit
   failing either actual S-box derivative equation.
6. Sum multiplicities in a map indexed by the six carry bits and
   the last three E tags. Enforce equality with the guessed
   boundary E tags on digits 5, 6 and 7. Final carries are free
   (all additions are modulo 2^32).

Thus each valid 32-bit r has one accepted weighted transfer path
and one cyclic seed; conversely every accepted path reconstructs
the eight digits of one real valid r. This is the intended
**mathematical exactness argument**. What has been proved in Lean
so far is the local tagged semantics and rotation identity, not
the executable counting correspondence.

Code files:
- TaggedCarryWord.lean: exact, sequential eight-step g + XOR
  derivative reconstruction; imported by Magma.lean.
- Rotate11Nibble.lean: exact post-rotation nibble formula, including
  a specialized statement for an arbitrary eight-element S-box
  tag array; also root-imported.
- fixed_middle_transfer.py: actual 8-nibble weighted transfer and
  optional exact #SMT enumeration of r at fixed h.
- fixed_middle_regression.py: deterministic actual witnesses,
  2^32 zero-difference mass, and independent zero-fiber checks.
- fixed_middle_subcube.py: finite sum over low-bit variants of h
  and an INDEPENDENT Z3 model enumerating (r,z) jointly.

## Reproducible fixed-key results

All rows use the real 32-bit RFC 8891 Magma round function and
the existing **Lean-certified** five-round positive witnesses:

| Witness | Fixed h | Exact C(h) by DP | Exhaustive independent Z3 |
|---|---|---:|---:|
| 1-hot → 4-hot | 0x10f8fac2 | 16 | 16 |
| 2-hot → 3-hot | 0x6084f2c7 | 96 | 96 |

Each takes around 0.002 seconds to count at fixed h in the
initial Mac benchmark; maximum frontier **18 states**. Every
2048 boundary seed was considered, not sampled. All-zero input
and output differences (a=b=0) yielded exactly **2^32** r values
per fixed h on BOTH actual fixed key sets, with a frontier <=4.

More demanding exact weighted sums with upper bits of h fixed:

| Number of varying low bits of h | h choices | 1-hot→4-hot | 2-hot→3-hot |
|---|---:|---:|---:|
| 4 | 16 | 48 (Z3: 48) | 288 (Z3: 288) |
| 8 | 256 | 96 (Z3: 96) | 576 (Z3: 576) |

The 8-bit subcube required approximately 0.61 seconds per
fixture for the weighted DP, plus independent Z3 enumeration
(approximately 0.10 and 0.43 seconds respectively). This
prototype is NOT claiming to be faster than Z3 on these tiny,
easy-to-enumerate slices.

In addition, deterministic sampling of 64 changed middle h
words per fixture found 62 and 57 zero conditional fibers,
respectively. Eight sampled fibers per fixture were separately
exhausted by Z3, with exact agreement including zero counts.
These are sample-specific observations, NOT rates of impossible
full-round endpoint differentials.

## Reproduce

    lake build Magma.Differential.RoundFunction.Rotate11Nibble

    python3 Magma/Differential/FiveRounds/Experiments/fixed_middle_transfer.py \
      --fixture 0 --z3-check \
      --output Magma/Differential/FiveRounds/Experiments/fixed_middle_transfer_0.json

    python3 Magma/Differential/FiveRounds/Experiments/fixed_middle_transfer.py \
      --fixture 1 --z3-check \
      --output Magma/Differential/FiveRounds/Experiments/fixed_middle_transfer_1.json

    python3 Magma/Differential/FiveRounds/Experiments/fixed_middle_regression.py \
      --samples-per-fixture 64 --z3-checks-per-fixture 8

    python3 Magma/Differential/FiveRounds/Experiments/fixed_middle_subcube.py \
      --fixture 0 --subcube-bits 8 --z3-model-cap 1000

    python3 Magma/Differential/FiveRounds/Experiments/fixed_middle_subcube.py \
      --fixture 1 --subcube-bits 8 --z3-model-cap 1000

All command outputs have reproducible JSON summaries next to
their scripts. Z3 has an explicit timeout; UNKNOWN is not UNSAT.

## Next actual mathematical/computational gap

Full five-round outer DDT is the sum of all C(h) over the
**2^32 middle base words h**. Simply running fixed-h DP
2^32 times is NOT a tractable DDT algorithm. Making the middle
base S-box tags U_i symbolic again introduces a second delayed
cyclic stream (naively 22 bits of guessed E/U boundary tags,
plus six carry bits). To solve this, find a variable-elimination
ordering or a compressed weighted transfer that eliminates h
**inside the local join**, instead of enumerating its values.

**2026-11-03 update:** The later joint_middle_transfer.rs
now eliminates h INSIDE a two-tag-stream weighted automaton,
rather than invoking this fixed-h DP 2^32 times.
It computed full fixed-key DDT counts 768 and 30,720, both
independently exhausted by Z3.
See [JOINT_MIDDLE_TRANSFER.md](JOINT_MIDDLE_TRANSFER.md).
The exact weighted Rust algorithm still needs a Lean
counting-bijection theorem. The nine-round SAT/motif branch
remains frozen.
