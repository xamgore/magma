# Genuine 32-bit-word Magma repeated-key windows: 600-second solver audit

Date: 2026-11-05.
Goal: recover a SMALL set of repeated 32-bit subkeys from chosen/known
plaintext/ciphertext pairs, rather than distinguish full Magma
from an ideal random permutation.

IMPORTANT THREAT MODEL:
- These are isolated 4..8-round ORDINARY Feistel G sequences,
  *not* the true full 32-round RFC schedule with all eight
  independent subkey words and its terminal GStar.
- Each named key A/B/C is an independent UNKNOWN 32-bit word.
  Every occurrence of that name is exactly the SAME Z3 variable.
- One secret tuple is fixed across the 2-4 input/output pairs.
- All g operations are true RFC 8891 32-bit modular addition,
  all EIGHT original Sboxes, and ROL11.
- A short isolated block with terminal GStar would have a
  publicly swapped output compared to our ordinary G convention.
- No reduced-width toy cipher and NO related-key oracle is used.
- Kernel-checked Lean proofs of exact low-round identities
  already exist in Magma/Differential/RepeatedKeys/RepeatedKeyThreeRound.lean.

Machine: Igors-MacBook-Pro.local, 16 logical CPUs, 48 GiB RAM,
Z3 5.0.0, Python 3.14. The reported times are ONE deterministic
instance per row, not a statistical distribution or complexity bound.

## Actual models

1. Direct Store/Select Sbox Z3: repeated_key_long_smt.py
   The actual 16-entry 4-bit RFC Sbox is encoded by Z3
   Store/Select into an array, then g computes 32-bit
   ADD, Sbox and ROL11. Iterate all rounds directly,
   equate observed output halfwords.
2. Direct Boolean-ANF Sboxes: repeated_key_anf_smt.py
   Each original 4-bit Sbox is represented by the
   UNIQUE Mobius/ANF polynomial in four Boolean
   input bits. Exhaustive checks cover all 8*16
   Sbox input/output entries; 100 full-word native
   g checks also verify the implementation.
3. Bidirectional symbolic midpoint: repeated_key_mitm_smt.py
   Compute prefix using real G forward, suffix using
   real G^-1 backward and require same exact full
   64-bit midpoint state for every known pair.
   Both sides SHARE the same key variables.
   This is a SAT factorization, NOT an independent-DDT
   Markov approximation and NOT classic exhaustive MITM.
4. One-dimensional Feistel recurrence: repeated_key_local_smt.py
   For x_-1=L,x_0=R,x_{j+1}=x_{j-1} XOR g_{key_j}(x_j),
   introduce one unknown 32-bit x_i per interior stage.
   Constrain x_{n-1}=U,x_n=V for observed ciphertext (U,V).
   Same key variables reused across stages AND pairs.

Lean:
Magma/Differential/RepeatedKeys/RepeatedKeySolverEncoding.lean has kernel-checked
laws that (i) this local recurrence is logically equivalent
to actual native G, (ii) reverse G is exact GEquiv.symm,
and (iii) forward-prefix equality with inverse-suffix
is iff correctness of full composed cipher.
This proves the mathematical formulations, not the external
Z3 implementation or a solver's heuristic runtime.

SAT means Z3 FOUND one candidate key and native Python g
replay confirmed the complete 4-8 round ciphertext under
that candidate for EVERY observed pair. SAT does NOT prove
there are no other keys. The optional second-model check
adds a disequality on all key words: only UNSAT proves
uniqueness for that observed instance.
UNKNOWN is a hard timeout; not proof of impossibility.

## Main independently replayed experiments (seed 4106)

Schedule   Key bits  Known data           Method   Result   Solver seconds
ABAB          64     2 arbitrary pairs    bidir ANF   SAT    0.067
ABABB         64     2 arbitrary pairs    bidir ANF   SAT    1.472
ABAABA        64     2 arbitrary pairs    bidir ANF   SAT  110.704
ABABBA        64     2 arbitrary pairs    bidir ANF   SAT  539.663
ABABBA        64     3 pairs, each R=0    bidir ANF   SAT   20.707
ABAABA        64     3 pairs, each R=0    bidir ANF   SAT   27.848
ABABBA        64     3 pairs, each R=0    local ANF   SAT   40.206
ABCABC        96     2 arbitrary pairs    direct array UNKNOWN 600
ABCABC        96     2 arbitrary pairs    direct ANF   UNKNOWN 600
ABCABC        96     2 arbitrary pairs    bidir ANF    UNKNOWN 600
ABCABC        96     3 pairs, each R=0    bidir ANF    UNKNOWN 600
ABCABC        96     2 arbitrary pairs    local ANF    UNKNOWN 600
ABCABC        96     3 pairs, each R=0    local ANF    UNKNOWN 600
ABABBA        64     2 arbitrary pairs    direct array UNKNOWN 600
ABABBA        64     2 arbitrary pairs    direct ANF   UNKNOWN 600
ABAABA        64     2 arbitrary pairs    direct array UNKNOWN 600
ABAABA        64     2 arbitrary pairs    direct ANF   UNKNOWN 600
ABABBAA       64     3 pairs, each R=0    bidir ANF    UNKNOWN 600
ABABBAAB      64     3 pairs, each R=0    bidir ANF    UNKNOWN 600

Further bounded controls:
- ABAB 2 arbitrary pairs: exact uniqueness (second distinct
  key UNSAT in ~0.259 seconds after SAT).
- ABABBA, 2 arbitrary pairs: distinct-key second query UNKNOWN
  after extra 10 seconds; key uniqueness NOT certified.
- ABAABA, 2 arbitrary pairs: distinct-key second query UNKNOWN
  after extra 10 seconds; key uniqueness NOT certified.
- ABABBA, 3 R=0 pairs: distinct-key second query UNKNOWN
  after extra 120 seconds; key uniqueness NOT certified.
- ABABBA, 3 arbitrary pairs: bidir ANF UNKNOWN at 180s.
- ABABBA, 2 pairs R=0: bidir ANF UNKNOWN at 180s.
- ABCABC, 3 R=0 pairs: bidir ANF UNKNOWN at 120s.
- ABCABC, 4 R=0 pairs: both bidir ANF and local ANF
  UNKNOWN at 180s.
- ABABBAA, 4 R=0 pairs: bidir ANF UNKNOWN at 180s.
- ABABB, 2 arbitrary pairs: local ANF SAT in 0.442s.
- ABABBA, 2 arbitrary pairs: local ANF UNKNOWN at 60s.

Thus more pairs and/or constant right input are NOT
monotonically guaranteed to make the solver faster.
The 20.7s vs 539.7s examples change BOTH number of
pairs and their chosen input pattern. The controlled
additional runs at 180s are consistent with sensitivity
to observation selection, but are not a distributional
speed-up theorem. Results are single deterministic
instances (same secret word tuple where applicable).

For seed 4106 with two key names, the secret tuple
is A=0x5a2203a8, B=0xde3124d4. All recovered-key
values in SAT rows matched the generated secret tuple
and were independently verified by actual Python RFC g.
The chosen R=0 inputs have differing random L values.

ABABBA is NOT a palindrome:
reverse(ABABBA) = ABBABA.
The actual short true palindrome here is ABAABA.
The true RFC full-32 schedule is different from BOTH.

## Reproduce exact jobs

  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_long_smt.py --pattern ABABBA --pairs 2 --seed 4106 --timeout 600000
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_anf_smt.py --pattern ABAABA --pairs 2 --seed 4106 --timeout 600000
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py --pattern ABABBA --pairs 2 --seed 4106 --timeout 600000 --encoding anf
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py --pattern ABABBA --pairs 3 --seed 4106 --timeout 600000 --encoding anf --input-mode zero-right
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py --pattern ABCABC --pairs 2 --seed 4106 --timeout 600000 --encoding anf
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py --pattern ABABBAA --pairs 3 --seed 4106 --timeout 600000 --encoding anf --input-mode zero-right
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_mitm_smt.py --pattern ABABBAAB --pairs 3 --seed 4106 --timeout 600000 --encoding anf --input-mode zero-right
  python3 Magma/Differential/RepeatedKeys/Experiments/repeated_key_local_smt.py --pattern ABABBA --pairs 3 --seed 4106 --timeout 600000 --encoding anf --input-mode zero-right
  lake build Magma Diffan

The full native RFC 32-round 256-bit master-key attack
remains OPEN. A short 2-word repeated Feistel schedule
can be far easier than an eight-word 32-round schedule.
Search slowdown at 7 rounds under 600s is a measurement
of this solver under this model, not a mathematical
lower bound on key recovery.

Further acceptance gate: derive a new exact key-word
elimination rule at 6+ rounds or a demonstrably
scalable symbolic projector; do not extrapolate
isolated SAT success to a full-cipher break.
