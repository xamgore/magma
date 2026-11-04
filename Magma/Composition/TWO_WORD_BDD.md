# Two-word BDD and canonical branch experiment (2026-11-04)

Status: exact 8-bit-word toy counting with a 13.9x smaller
per-branch BDD allocation. A scalable full 32-bit RFC Magma
seven-round weighted counter remains OPEN.

## Exact elimination of redundant delta variables

For ordinary fixed-key five-round Feistel let
P=F_k1 o F_k0, R=F_k4 o F_k3 o F_k2.
For fixed input difference alpha and output beta, the complete
real intermediate base u after P determines its XOR difference:

    delta_alpha(u) = P(P^(-1)(u) XOR alpha) XOR u.

Thus the exact DDT is

    D5(alpha,beta) =
      SUM_u [R(u XOR delta_alpha(u)) XOR R(u) = beta].

Only 2w input base bits are independent, not 4w freely
guessed base+delta bits. This is exact, not an independence
approximation. Implementation: two_word_bdd_probe.py.
The code supports toy word lengths 4,8,12,16, using real RFC
4-bit S-box values and modular carries, NOT 32-bit RFC
Magma's complete round function.

## S-box encoding benchmarks

sbox_bdd_optimizer.py compares equivalent Boolean encodings:
16 minterms, exact algebraic normal form (ANF, Moebius
transform), and Shannon decomposition.

For the positive 8-bit word toy with keys [1,2,3,4,5],
rotation 3, input (0,1) and output (0xd7,0):

| Encoding | Completed DDT | Total BDD nodes created |
|---|---:|---:|
| Minterms | 2 | 1,192,550 |
| ANF | 2 | 979,931 |
| Shannon | 2 | 1,144,651 |

The ANF improvement is about 18% for this fixture only.

## Canonical representative of each XOR pair

For fixed nonzero alpha=(0,a), the two inputs x and
x XOR alpha contribute equally to the DDT. Fix the
least significant toggled bit in the input right word
to 0, count the remaining solutions and multiply by 2.

This is an exact bijection of unordered pairs; no
models are discarded or probabilistically approximated.

canonical_branch_bdd.py further partitions an independent
four-bit base nibble into 16 disjoint cases, sums all
completed counts, and returns LIMIT if ANY case is
incomplete.

| Four conditioned input-base bits | Exact DDT | Complete branches | Max nodes per branch | Total nodes |
|---|---:|---:|---:|---:|
| left bits 0..3 | 2 | 16/16 | 89,547 | 1,383,913 |
| left bits 4..7 | 2 | 16/16 | 95,151 | 1,504,786 |
| right bits 4..7 | 2 | 16/16 | 70,510 | 1,097,218 |

The best case reduces peak table allocation from the
979,931 monolithic ANF nodes to 70,510 per branch:
about **13.9x lower peak memory proxy**, without claiming
a comparable runtime gain. Total work remains similar.

## Independent three-nibble 12-bit-word reference

three_nibble_exhaustive.rs exhaustively checks all
2^24=16,777,216 input states of a five-round Feistel
using the first THREE actual RFC S-boxes, 12-bit modular
addition and rotation 7, keys [1,2,3,4,5].

    D5((0,1),(0x79,0)) = 548.

This is a toy reference, NOT the 32-bit RFC Magma DDT.
Canonical branch BDD reaches LIMIT at 250,000 BDD
nodes already in its first 12-bit branch. Most
eight-bit conditioned 12-bit BDDs also hit LIMIT at
400,000 nodes; a single zero subcube is NOT a full DDT.
The weak_bdd_probe.py garbage-collection experiment
also hits real live-node limits for 8/12-bit toy circuits.
Stronger structurally local elimination remains required.

## Negative control: 9-round reflection and all keys

The reflected nine-round toy with 4-bit words,
keys indexed [4,5,6,7,7,6,5,4,3] and real first RFC
S-box (rotation 1) has NO key-universal zero among
the 225 tested nonzero opposite boundary endpoints
(a,0)->(0,b), a,b in {1,..,15}.

reflection_toy_key_coverage.rs found an explicit
key/plaintext witness for every endpoint after only
18 different key assignments (out of 16^4 possible).
reflection_toy_key_coverage_verify.py independently
replays all 225 witnesses through nine genuine toy
Feistel rounds in Python, and checks the 8-round
palindrome difference. The 225 concrete tuples
are stored in reflection_toy_225_witnesses.json.

This is a CONSTRUCTIVE support result for a FOUR-BIT
toy, not proof of universal support for real Magma.
It demonstrates why fixed-key zeros are not sufficient
evidence of key-universal impossible differentials.

## Next gate

Use early output constraints, nibble-local project-join,
or a compressed shared carry/tag interface. A successful
full-width method must return COMPLETE integer counts
matching the independent 2,0,0,8 fixed-key controls.
No inference of zero is permitted from LIMIT.
Preserve the broad nine-round SAT and irrelevant formal
Rust-weight freezes.

## Reproduction

    python3 Magma/Composition/two_word_bdd_probe.py --max-word-bits 8 --max-nodes 1500000
    python3 Magma/Composition/sbox_bdd_optimizer.py --max-nodes 1500000
    python3 Magma/Composition/canonical_branch_bdd.py --max-nodes 250000
    rustc -O Magma/Composition/three_nibble_exhaustive.rs -o /tmp/magma_three_nibble
    /tmp/magma_three_nibble
    python3 Magma/Composition/reflection_toy_key_coverage_verify.py
    lake build Magma
