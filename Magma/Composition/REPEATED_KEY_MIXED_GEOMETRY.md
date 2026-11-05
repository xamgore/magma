# Repeated-key mixed XOR / modular constraints, genuine 32-bit RFC Magma g

Verified 2026-11-05. Scope: ordinary 32-bit-word Feistel G rounds
with ALL eight real RFC Sboxes, real addition mod 2^32 and ROL11.
The RFC 32-round cipher uses eight INDEPENDENT 32-bit key words,
the actual 32-round 8-key chronological/reversed schedule and
a final GStar, rather than the short synthetic sequences here.

**This is key-recovery for REDUCED 2-/3-round schedules**, NOT
a fixed-key cryptanalytic advantage against the genuine 32-round
256-bit master-key RFC cipher.

Lean: Magma/Diffan/RepeatedKeyThreeRound.lean.
Independent program: Magma/Composition/repeated_key_mixed_geometry.py.
Bounded 4-7-round SMT: Magma/Composition/repeated_key_smt_scaling.py.

## Correct semantics

Let g_k(x)=ROL11(S(x+k mod 2^32)) using real RFC Sboxes.
Ordinary Feistel G_k(L,R)=(R,L XOR g_k(R)).
All formulas here use chronological ordinary G rounds; a shortened
cipher whose terminal round is RFC-style GStar has its output
halves publicly swapped relative to the final ordinary G state.
Do not silently compare incompatible endpoint conventions.

The difference interface changes INSIDE the round:

- XOR across Feistel and after Sboxes/rotation.
- Modular addition to encode two evaluations x+k, y+k.
- Two independent carries for each pair of additions.
- Equality of the SAME unknown key word across repeated rounds.

This is a key-CSP, not multiplication of marginal DDT probabilities.

## Two rounds: no repetition advantage

For a,b (not necessarily equal) and chosen (L,R),
  G_b(G_a(L,R)) = (U,V) where
  U = L XOR g_a(R)
  V = R XOR g_b(U).

Define exact inverse of key-to-g-value:
  keyFor(x,y) = S^-1(ROR11(y)) - x (mod 2^32).
Then
  a = keyFor(R, U XOR L),
  b = keyFor(U, V XOR R).
This recovers BOTH independent 32-bit keys from ONE known pair.
So the two-round result is trivial Feistel leakage, not evidence
of cryptanalytic weakness induced by repeating keys.
Independent 250-trial verification for a,a and a,b passed.

## Three rounds: genuine coupling advantage of a,b,a

For plaintext (L,R) and output (Q,U) after chronological a,b,a:
  P = L XOR g_a(R)
  Q = R XOR g_b(P)
  U = P XOR g_a(Q).

Eliminate the hidden P and b:
  g_a(R) XOR g_a(Q) = L XOR U.
This is a NECESSARY observable equation on a ALONE.

Write target = ROR11(L XOR U). Since rotation is linear for XOR:
  S(R+a) XOR S(Q+a) = target.

The variables a,R,Q are 32-bit words; addition is mod 2^32.
At nibble index i=0..7, guess a_i in 0..15,
track BOTH true carries c_i^R,c_i^Q,
  u_i=R_i+a_i+c_i^R
  v_i=Q_i+a_i+c_i^Q
  S_i(u_i mod 16) XOR S_i(v_i mod 16) = target_i
  c_(i+1)^R=floor(u_i/16)
  c_(i+1)^Q=floor(v_i/16).
Use one common guessed a_i ACROSS ALL observed pairs and all
their independent carry chains. This enumerates exactly
the candidate outer subkeys a satisfying the observable
equations; no heuristics or DDT marginal independence.

For every candidate a,
  P=L XOR g_a(R),
  b=keyFor(P, Q XOR R).
Replay full 3-round G_a,G_b,G_a on all pairs and retain
only keys yielding exactly the recorded outputs.

The binary key space has 2^64 candidate pairs, but this
procedure does not guess b. Empirical COST is the number
of 4-bit local tests, not total full-key trial encryption.

250 independent random a,b and random chosen input pairs:
- Two known plaintext/ciphertext pairs:
    236 cases retained exactly ONE (a,b);
     14 cases retained exactly TWO (a,b).
    Mean 238.976 nibble candidates tested; max 4880.
- Three known plaintext/ciphertext pairs:
    ALL 250 cases retained exactly ONE (a,b), always the
    actual key pair.
    Mean 131.776 nibble candidates tested; max 240.
- One pair is often poorly informative: three runs hit
    the explicit 100,000-final-outer-key-candidate guard.
    The other runs may have tens of thousands of answers.
    Such cases are marked LIMIT and never falsely claimed
    complete.
- The independent genuine-RFC Python g evaluator and
  local g inverse are cross-checked on random 32-bit
  values in each trial.

These are FINITE experimental results, not a universal
claim that three pairs uniquely identify every (a,b).
The exact algebraic necessary equation is independently
kernel-proved in Lean:
  three_repeated_outer_key_equation,
  three_candidate_necessary,
  three_middle_function_value.

## Four rounds: a,b,a,b

The repeated-key equations now involve a hidden
intermediate state. Let
  P=L XOR g_a(R)
  Q=R XOR g_b(P)
  U=P XOR g_a(Q)
  V=Q XOR g_b(U).

The repeated b gives
  g_b(P) XOR g_b(U) = R XOR V.
BUT P depends on unknown a. Hence there is no direct
observable single-key equation analogous to the
3-round one.

An exact parameterization of ALL four-round solutions
uses hidden Q as free 32-bit parameter. For a proposed Q:
  b = keyFor(U,V XOR Q)
  P = S^-1(ROR11(Q XOR R)) - b (mod 2^32)
  a = keyFor(R,P XOR L)
  check g_a(Q) == U XOR P and replay all observations.

It is a mathematically exact candidate parameterization,
but an enumeration over all Q costs up to 2^32
candidate trials. The code validates actual known
hidden Q on 20 genuine full-word instances; it does
NOT claim that the search over 2^32 was performed.

Lean:
  four_repeated_state_equations,
  four_repeated_inner_key_equation.

## Concrete SMT behavior for 4..7 short alternating rounds

A separate complete BITVECTOR model encodes both unknown
32-bit keys, all actual Sboxes via finite Z3 arrays,
32-bit additions, rotations and exact Feistel rounds.
Two independent input/output pairs are imposed as
key constraints, no guessed internal state.

Reproduce:
  python3 Magma/Composition/repeated_key_smt_scaling.py

Deterministic seed 40324, 2 known input/output pairs,
one instance per round count:
  4 rounds: SAT, correct original key found in 2.119 s
            under 5000ms solver cap;
  5 rounds: SAT, correct original key found in 5.201 s
            under 6500ms solver cap;
  6 rounds: UNKNOWN after 6515ms under 6500ms cap;
  7 rounds: UNKNOWN after 6515ms under 6500ms cap.
Exact durations are hardware/solver dependent.

SAT means one valid candidate found, NOT that the key
is unique; recovered candidates were independently
replayed. UNKNOWN is a bounded failed search, NOT
proof of absence or an exponential lower bound.
The SMT budget must not be silently extended.

## Research implications

POSITIVE: a,b,a exhibits a key-elimination identity
from publicly observed state halves; exact modular
carry constraints can recover repeated words far
below 2^64 exhaustive candidate trials on sampled
instances. This is actual KEY FILTERING, NOT
a random-permutation distinguisher.

NEGATIVE: reusing only two unknown 32-bit words is
a very weak reduced-key experimental structure.
At four rounds the outer-key-only equation disappears
because an argument becomes hidden. There is NO
evidence that this technique solves genuine full
32-round Magma with eight unknown words.

NEXT falsifiable objective: identify an accessible
observed algebraic relation eliminating a key word
for a LONGER repeated-key Feistel window, or a small
symbolic projection over key bits that permits
provably correct class exclusion. Compare resulting
time against 2^(number of unknown key bits), not
against a generic random-permutation distinguisher.
