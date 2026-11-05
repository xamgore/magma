# Three full-text papers: relevance to exact Magma fiber composition

Source: three PDFs supplied in the research conversation on 2026-11-03.
This is a **research reading note**, not proof of priority or exhaustive
literature coverage. The original PDFs are *not* distributed in this repo
(copyright/license terms differ). Distinguish differential
**characteristics/trails** from the **exact DDT of a fixed-key cipher**.

## I. Liu, Li, Jiao, Wang — CDDT / CLAT

**A New Method for Searching Optimal Differential and Linear Trails in ARX
Ciphers**, IEEE Transactions on Information Theory, DOI
[10.1109/TIT.2020.3040543](https://doi.org/10.1109/TIT.2020.3040543).
The uploaded PDF has an older 2015 journal template in its header,
but states manuscript received 2019, revised 2020, and accepted for
publication with the 2020 DOI. Do not infer publication year **2015**
from its PDF title or boilerplate header.

- Sections II–III: divide n-bit modular addition into small carry-linked
  t-bit additions; use *carry-bit-dependent difference distribution
  tables* (CDDT) and CLAT. Each boundary carry is a finite state.
- Section IV: order candidate local transitions by weight and use
  Matsui-style branch-and-bound to find optimal *trails* in ARX designs.
- **For Magma:** re-use this finite-state, carry-indexed table abstraction.
  Our true local state additionally emits the S-box **base output tag**
  and **difference tag** simultaneously. Unlike merely selecting the
  best trail, our objective is to **sum exact integral multiplicities**.
  Never multiply independently optimized local DDTs without preserving
  correlations.

## II. Qin & Wu — non-independent consecutive modular additions

**Towards non-independence of modular additions in searching differential
trails of ARX ciphers: new automatic methods with application to SPECK
and Chaskey**, arXiv:2203.09741v1 (2022).

- Sections 3–4: analyze contradictions between constraints from adjacent
  additions; the intermediate base state after a conditioned first
  addition is generally NOT uniformly random.
- They use SAT for actual feasibility and **#SAT for more accurate
  probabilities** of trails containing consecutive modular additions.
- **For Magma:** this is the closest conceptual warning about losing
  state correlations. Reproduce *strict coarse-join defect*
  fixtures whenever changing the compressed interface. Independent
  SMT counting of (r,z) is an appropriate external oracle for small
  exact fibers and the present fixed-middle-h subcubes.
- But the paper studies ARX additions and related-key trails,
  not an established exact fixed-RFC-key Magma five-round DDT engine.

## III. Kwon & Song — multistage characteristic graph

**Computing the Differential Probability of a Word-Based Block Cipher**,
*Cryptography* 9(2), 42 (2025),
DOI [10.3390/cryptography9020042](https://doi.org/10.3390/cryptography9020042).
Open access under CC BY (as stated in the uploaded PDF).

- Sections 3–4: construct multistage graphs connecting intermediate
  differences, with restricted activity patterns; count the
  **exact number of maximum-probability differential characteristics**
  within the specified pattern, then include lower-probability
  characteristics to improve estimates of differential probability.
- **Critical distinction:** their exact *characteristic count* and
  resulting estimates are NOT an exact fixed-key block-cipher DDT.
  It would be erroneous to equate a graph-path count over difference
  labels with the actual number of base pairs.
- **For Magma:** use sparse multistage graph construction, meet-in-the-middle,
  weighted path aggregation and pruning. Nodes need a certified
  *sufficient statistic* of the full (base,difference,carry,key-coupling)
  join; otherwise the graph may overcount, as our existing strict
  join-defect examples prove.

## Bottom-up action order

1. **Done:** kernel-prove tagged actual carry transitions and
   rotate-left-11 nibble wiring: `TaggedCarryWord.lean`,
   `Rotate11Nibble.lean`.
2. **Done experimentally:** exact weighted 32-bit fixed-middle-`h`
   fiber transfer; independent exhaustive #SMT regression for
   fixed `h` and 4-/8-bit subcubes; see
   [FIXED_MIDDLE_TRANSFER.md](../../FiveRounds/Experiments/FIXED_MIDDLE_TRANSFER.md).
3. **Done experimentally:** joint_middle_transfer.rs now
   eliminates the *full* 32-bit middle base `h` inside one
   weighted eight-nibble carry transfer, preserving both
   S-box tag streams and exact cyclic rotate-left-11 links.
   Full 5-round counts 768 and 30,720 were independently
   exhausted by Z3 and directly replayed as real Magma
   Feistel pairs; see JOINT_MIDDLE_TRANSFER.md.
4. **Still open formally:** prove the weighted DP ↔ full
   fixed-key fiber cardinality theorem in Lean (currently
   only local acceptance semantics are kernel-proved).
   Then compose correlated cores for seven/nine rounds.
   Distinguish computationally verified exact counts
   from kernel-certified count theorems.

Research novelty, if any, must be formulated at the precise point
of the **correlation-preserving, fixed-key, exact Magma fiber
composition**, not at the generic notions of carry automata, SAT,
or characteristic graphs.
