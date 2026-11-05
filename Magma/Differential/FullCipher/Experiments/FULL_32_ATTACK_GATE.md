# Attack-observability gate for full RFC 8891 Magma

Date: 2026-11-05. This is an **attack-model audit**.
No successful single-secret-key attack on full 32-round
Magma is claimed. All real-width tests use actual RFC
32-bit modular arithmetic, S-boxes, rotation, schedule
and final no-swap GStar. Frozen frontier/BDD/SAT
engineering has not been resumed.

## 1. Real and public 16-round distinguisher

Let E16 be 16 ORDINARY Feistel rounds with keys
[0..7,7..0], for ANY eight 32-bit key words; J
swaps the two 32-bit halves. Q16=J E16 is
H^-1 J H, so exactly 2^32 states satisfy

    E16(x) = J(x).

This is an actual UNKNOWN-KEY oracle predicate:
the attacker supplies x, observes 16-round ciphertext
and compares it with J(x). No H or subkeys are needed.

Lean: Magma/Differential/FullCipher/PalindromicOracle.lean:
  E16_matches_swap_iff_H_diagonal
  E16SwapMatchEquiv
  E16_has_exactly_two_pow_32_swap_matches
  all_64bit_states_count.

For a uniformly random 64-bit plaintext:
true E16 match probability exactly 2^-32.
For an ideal random 64-bit permutation:
single-query match probability exactly 2^-64.

For q uniformly chosen distinct inputs, true
success probability is exactly
  1 - binom(2^64-2^32,q) / binom(2^64,q).
For q=2^32 it is approximately 1-exp(-1)=0.632.
Ideal success is at most q/2^64=2^-32
by union bound. Complexity: roughly 2^32
chosen encryptions, at the 64-bit birthday scale.
For a truncated last GStar variant replace
the observable test by ciphertext=plaintext.

Independent real 32-bit RFC confirmation:
24 constructed positive x=H^-1(t,t) all replay
E16(x)=Jx; this construction REQUIRES the key
and is not itself an unknown-key oracle algorithm.
The Lean theorem establishes the counts without
enumerating 2^32 points.

## 2. Why the same test does NOT break full 32

The true full RFC cipher C32=Q16 H², hence

    Q16(H²(x))=H²(x)  iff  C32(x)=H²(x).

The RHS needs the UNKNOWN intermediate H²(x).
There is no supported substitution H²(x)=x
or H²(x)=Jx, and no accessible oracle for H².

In a 4-bit-word/8-bit-total-state one-Sbox
toy with 600 independent random eight-key vectors:
- every 16-round E16: exactly 16 E16(x)=Jx;
- full C32: mean 1.068333 fixed points C32(x)=x;
- full C32: mean 1.073333 swap matches C32(x)=Jx.

For q=16 distinct random input queries in 600
independent trials, observed successful trials:
  E16 swap test              395 / 600
  C32 identity test           35 / 600
  C32 swap test               41 / 600
  ideal random permutation    32 / 600.

This is only a small-toy diagnostic, NOT a
64-bit statistical claim or a no-attack theorem.
It falsifies the naive proposed transfer of
the 16-round *public* swap test to full C32.

## 3. Real full-32 related-key distinguisher

Define the 256-bit mask M containing 0x80000000
in EACH of the eight master-key words. Put
K'=K XOR M, t=0x8000000080000000.
The native RFC 32-round theorem gives

    E_K'(x XOR t)=E_K(x) XOR t

for ALL unknown K and chosen 64-bit x.
If the adversary HAS TWO related-key oracles
for K and K', they need only TWO encryption
queries to check this publicly observable identity.

Under the ideal-cipher model with independent
uniform random permutations for distinct keys,
conditional on the first output, exactly ONE
of the 2^64 second outputs passes. Therefore
the ideal false-positive probability is 2^-64.

Lean: Magma/Differential/FullCipher/RelatedKeyOracleDistinguisher.lean:
  full_rfc_related_key_two_query_distinguisher
  ideal_independent_second_output_one_matching_value
  ideal_output_alphabet_card.

This is a genuine RELATED-KEY distinguisher for
the full 32-round family. It is NOT key recovery
and NOT an ordinary single-unknown-key attack.
A user who cannot request the carefully related
second key cannot run it.

## 4. FORMAL no-go for using the key gauge alone

Difan/Observables/OracleObservableBarrier.lean proves that
for EVERY arbitrary state permutation f and ANY
bijective coordinate change e, there is a UNIQUE
formal partner g=e o f o e^-1 satisfying

    g(e(x))=e(f(x)).

Thus the bare claim of a gauge-related second key
places NO restriction on the original unknown f:
an arbitrary ideal permutation can always have a
formal partner. To derive a SINGLE-KEY distinguisher
one must use an additional Magma-specific property.

This is an exact theorem, not a simulation.
It does NOT establish any security of real Magma.

## 5. Search for cheap public operator identities

Magma/Differential/FullCipher/Experiments/public_oracle_word_gate.py
checks the TRUE RFC key from Appendix A.3 and
x=0x0123456789abcdef, using an independently
replayed 32-round encryption and inverse.

It exhausts ALL 12,285 nonempty freely reduced
operator words of length <=12 on the alphabet
{F=C_K, I=C_K^-1, J=public half-swap}, with
F I = I F = J J = identity already canceled.
NONE returns the base to itself.

Hence every purported UNIVERSAL all-key,
all-input identity of that form and length
has an explicit real RFC counterexample.
This is a reproducible computational check,
NOT a Lean-certified 12,285-theorem proof.

It does NOT eliminate statistical or XOR
relations, word identities involving other
operators, longer words, or some special keys.

## 6. Check cycle invariants in abstract size eight

A separate, complete ABSTRACT permutation
experiment (NOT real Magma) enumerates all
8!=40,320 arbitrary H on eight states and
computes C=H^-1 J H³ for a fixed J with
four fixed points and two transpositions.

Of the 20,160 even 8-state permutations,
14,416 occur. Thus not every exact permutation
is attainable. However ALL 12 EVEN CYCLE
TYPES have representatives. In this small
abstract model there is NO key-independent
cycle-type exclusion beyond parity.

This is NOT a theorem for 2^64 states.
For actual 64-bit state permutations, the
macro equation does imply sign(C32)=sign(J)
because sign(H^-1)sign(H³)=1. Here J has
2^31*(2^32-1) transpositions, hence is EVEN.
This one-bit parity invariant needs essentially
a full 2^64-entry codebook to observe and
is generic to big-state Feistel networks.
It is not an effective standard-model break.

## 7. Hard acceptance criteria for the next attack

A claim about the FULL native RFC 32-round
single-secret-key setting must provide:

1. An explicit publicly evaluable predicate
   on observed inputs and outputs, with no
   H, H², round keys or related-key oracle.
2. A full-32-round theorem for ALL keys,
   or a clearly bounded key-distribution bias.
3. A valid independent-ideal-64bit-permutation
   false-positive bound (no bogus DDT products).
4. Data/memory/time estimates, ideally below
   2^32 queries (the 64-bit birthday scale).
5. If claiming key recovery, a concrete
   reduction from the observable to candidates.

Full-32 single-secret-key distinguisher:
    OPEN / NOT FOUND.
Full-32 two-query related-key distinguisher:
    PROVED; strictly a different threat model.
Unknown-key 16-round palindrome distinguisher:
    PROVED; roughly 2^32-query scale.

The next hinge is to turn Q16(H²x)=H²x
into a genuine PUBLIC predicate without
reconstructing H², or derive a different
multi-point full-C constraint with a
random-permutation baseline. NO further
key-gauge classification is justified
without such an observability argument.
Design freeze F4 remains in force.

Reproduce:
  lake build Difan Magma
  python3 Magma/Differential/FullCipher/Experiments/macro_attack_gate.py
  python3 Magma/Differential/FullCipher/Experiments/public_oracle_word_gate.py
  lake env lean /tmp/AuditFullAttackGate.lean

Verified 2026-11-05:
  lake build Difan Magma PASS (18,749 jobs).
  All Python control scripts PASS.
  #print axioms on NINE new statements:
  - Palindromic match equivalence, exact 2^32
    count, 2^64 state size: ZERO native
    bv_decide and ZERO sorry; standard Lean
    propext/choice/quotient axioms as applicable.
  - Generic gauge-existence/uniqueness no-go:
    ZERO native bv_decide and ZERO sorry.
  - Ideal-key matching single-output count:
    ZERO native bv_decide and ZERO sorry.
  - Native RFC two-query related-key theorem:
    ZERO sorry; inherits precisely the named
    native bitvector-reflection axiom
    _native.bv_decide.ax_1_5 from the earlier
    symbolic 32-bit top-bit arithmetic proof.
  This is an explicit trusted-SAT caveat,
  not a claim of kernel-only certifiability.
